-- Prove2me | solution 1 for Erdos592.specker_omega_sq
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:57:50.845976+00:00
-- url     : https://prove2.me/submissions/381887bb-a276-4339-8a7f-e5b1da5b1450

import Definitions.Def_Erdos592_Defs
import Mathlib

set_option autoImplicit false

universe u

namespace Erdos592Sol

/-- Infinite Ramsey theorem for `k`-tuples (strictly increasing) with finitely many colours,
relative to an infinite ground set `S`. -/
theorem ramsey_tuples {ι : Type} [Finite ι] :
    ∀ (k : ℕ) (c : (Fin k → ℕ) → ι) (S : Set ℕ), S.Infinite →
      ∃ (N : Set ℕ) (i : ι), N ⊆ S ∧ N.Infinite ∧
        ∀ g : Fin k → ℕ, StrictMono g → (∀ t, g t ∈ N) → c g = i := by
  intro k
  induction k with
  | zero =>
    intro c S hS
    exact ⟨S, c (fun _ => 0), subset_rfl, hS, fun g _ _ => congrArg c (Subsingleton.elim _ _)⟩
  | succ k ih =>
    intro c S hS
    -- one step: peel off the least element of an infinite set
    have hstep : ∀ T : {T : Set ℕ // T ⊆ S ∧ T.Infinite},
        ∃ T' : {T : Set ℕ // T ⊆ S ∧ T.Infinite}, T'.1 ⊆ T.1 \ {sInf T.1} ∧
          ∃ i : ι, ∀ g : Fin k → ℕ, StrictMono g → (∀ t, g t ∈ T'.1) →
            c (Fin.cons (sInf T.1) g) = i := by
      intro T
      obtain ⟨N, i, hNsub, hNinf, hN⟩ := ih (fun g => c (Fin.cons (sInf T.1) g))
        (T.1 \ {sInf T.1}) (T.2.2.sdiff (Set.finite_singleton _))
      exact ⟨⟨N, hNsub.trans (Set.sdiff_subset.trans T.2.1), hNinf⟩, hNsub, i, hN⟩
    choose F hFsub col hcol using hstep
    let T : ℕ → {T : Set ℕ // T ⊆ S ∧ T.Infinite} := fun j => F^[j] ⟨S, subset_rfl, hS⟩
    have hT : ∀ j, T (j + 1) = F (T j) := fun j => Function.iterate_succ_apply' F j _
    let a : ℕ → ℕ := fun j => sInf (T j).1
    have hamem : ∀ j, a j ∈ (T j).1 := fun j => Nat.sInf_mem (T j).2.2.nonempty
    have hsub : ∀ j, (T (j + 1)).1 ⊆ (T j).1 \ {a j} := fun j => by
      rw [hT]; exact hFsub _
    have hanti : Antitone (fun j => (T j).1) :=
      antitone_nat_of_succ_le fun j => (hsub j).trans Set.sdiff_subset
    have hlt : ∀ j j', j < j' → a j < a j' := by
      intro j j' h
      have h1 : a j' ∈ (T (j + 1)).1 := hanti (Nat.succ_le_of_lt h) (hamem j')
      have h2 : a j' ∈ (T j).1 \ {a j} := hsub j h1
      exact lt_of_le_of_ne (Nat.sInf_le h2.1) (fun e => h2.2 e.symm)
    have ha : StrictMono a := fun j j' h => hlt j j' h
    obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber (fun j => col (T j))
    have hJ : (((fun j => col (T j)) ⁻¹' {i}) : Set ℕ).Infinite := Set.infinite_coe_iff.1 hi
    refine ⟨a '' ((fun j => col (T j)) ⁻¹' {i}), i, ?_, hJ.image ha.injective.injOn, ?_⟩
    · rintro _ ⟨j, -, rfl⟩
      exact (T j).2.1 (hamem j)
    · intro g hg hgN
      obtain ⟨j, hj, hgj⟩ := hgN 0
      have hgtail : ∀ t : Fin k, g t.succ ∈ (T (j + 1)).1 := by
        intro t
        obtain ⟨j', hj', hj'e⟩ := hgN t.succ
        have hlt' : a j < a j' := by
          rw [hj'e, hgj]; exact hg (Fin.succ_pos t)
        have : j < j' := ha.lt_iff_lt.1 hlt'
        exact hanti (Nat.succ_le_of_lt this) (hj'e ▸ hamem j')
      have key := hcol (T j) (fun t => g t.succ) (fun s t hst => hg (Fin.succ_lt_succ_iff.2 hst))
        (by rw [← hT]; exact hgtail)
      have hcons : g = Fin.cons (a j) (fun t => g t.succ) := by
        rw [hgj]; exact (Fin.cons_self_tail g).symm
      rw [hcons]
      rw [key]
      exact hj


lemma sm4 {a b c d : ℕ} (h1 : a < b) (h2 : b < c) (h3 : c < d) : StrictMono ![a, b, c, d] := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> simpa

open Classical in
/-- The four-bit colour of an increasing 4-tuple recording the colour of the four
"interaction forms" of pairs of points. -/
noncomputable def col4 (R : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop) (g : Fin 4 → ℕ) :
    Bool × Bool × Bool × Bool :=
  (decide (R (toLex (g 0, g 1)) (toLex (g 2, g 3))),
   decide (R (toLex (g 0, g 2)) (toLex (g 1, g 3))),
   decide (R (toLex (g 0, g 3)) (toLex (g 1, g 2))),
   decide (R (toLex (g 0, g 1)) (toLex (g 0, g 2))))

open Classical in
lemma col4_iff (R : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop) {N : Set ℕ} {i : Bool × Bool × Bool × Bool}
    (hN : ∀ g : Fin 4 → ℕ, StrictMono g → (∀ t, g t ∈ N) → col4 R g = i)
    {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N) (hd : d ∈ N) :
    (R (toLex (a, b)) (toLex (c, d)) ↔ i.1 = true) ∧
    (R (toLex (a, c)) (toLex (b, d)) ↔ i.2.1 = true) ∧
    (R (toLex (a, d)) (toLex (b, c)) ↔ i.2.2.1 = true) ∧
    (R (toLex (a, b)) (toLex (a, c)) ↔ i.2.2.2 = true) := by
  have h := hN ![a, b, c, d] (sm4 hab hbc hcd) (by
    intro t; fin_cases t <;> simpa)
  rw [← h]
  simp [col4]
  exact ⟨decide_eq_true_iff.symm, decide_eq_true_iff.symm, decide_eq_true_iff.symm,
    decide_eq_true_iff.symm⟩


/-- The point `(ν m, ν n)`. -/
def pt (ν : ℕ → ℕ) (m n : ℕ) : ℕ ×ₗ ℕ := toLex (ν m, ν n)

lemma pt_inj {ν : ℕ → ℕ} (hν : StrictMono ν) {m n m' n' : ℕ} :
    pt ν m n = pt ν m' n' ↔ m = m' ∧ n = n' := by
  simp [pt, hν.injective.eq_iff]

/-- Core of Specker's theorem for `ω²` in coordinates: a symmetric relation on `ℕ ×ₗ ℕ`
whose complement (on distinct points) has no triangle admits a copy of `ℕ ×ₗ ℕ` on which it
holds between any two distinct points. -/
theorem specker_core (R : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop) (hsymm : ∀ x y, R x y → R y x)
    (htri : ∀ x y z : ℕ ×ₗ ℕ, x ≠ y → y ≠ z → x ≠ z → ¬ R x y → ¬ R y z → ¬ R x z → False) :
    ∃ φ : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ, StrictMono φ ∧ ∀ u v, u ≠ v → R (φ u) (φ v) := by
  classical
  obtain ⟨N, i, -, hNinf, hN⟩ := ramsey_tuples 4 (col4 R) Set.univ Set.infinite_univ
  obtain ⟨i0, i1, i2, i3⟩ := i
  have hNinf' : (Set.ofPred (· ∈ N)).Infinite := hNinf
  obtain ⟨ν, hν, hνN⟩ : ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∀ n, ν n ∈ N :=
    ⟨Nat.nth (· ∈ N), Nat.nth_strictMono hNinf', fun n => Nat.nth_mem_of_infinite hNinf' n⟩
  have H : ∀ m n p q : ℕ, m < n → n < p → p < q →
      (R (pt ν m n) (pt ν p q) ↔ i0 = true) ∧ (R (pt ν m p) (pt ν n q) ↔ i1 = true) ∧
      (R (pt ν m q) (pt ν n p) ↔ i2 = true) ∧ (R (pt ν m n) (pt ν m p) ↔ i3 = true) :=
    fun m n p q h1 h2 h3 =>
      col4_iff R hN (hν h1) (hν h2) (hν h3) (hνN m) (hνN n) (hνN p) (hνN q)
  have hne : ∀ m n m' n' : ℕ, (m ≠ m' ∨ n ≠ n') → pt ν m n ≠ pt ν m' n' := by
    intro m n m' n' h e
    have := (pt_inj hν).1 e
    omega
  -- all four forms are red
  have f0 : i0 = true := by
    by_contra h0
    have hn : ∀ m n p q, m < n → n < p → p < q → ¬ R (pt ν m n) (pt ν p q) :=
      fun m n p q h1 h2 h3 hR => h0 ((H m n p q h1 h2 h3).1.1 hR)
    exact htri (pt ν 0 1) (pt ν 2 3) (pt ν 4 5) (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega))
      (hne _ _ _ _ (by omega)) (hn 0 1 2 3 (by omega) (by omega) (by omega))
      (hn 2 3 4 5 (by omega) (by omega) (by omega)) (hn 0 1 4 5 (by omega) (by omega) (by omega))
  have f1 : i1 = true := by
    by_contra h1
    have hn : ∀ m n p q, m < n → n < p → p < q → ¬ R (pt ν m p) (pt ν n q) :=
      fun m n p q h1' h2 h3 hR => h1 ((H m n p q h1' h2 h3).2.1.1 hR)
    exact htri (pt ν 0 3) (pt ν 1 4) (pt ν 2 5) (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega))
      (hne _ _ _ _ (by omega)) (hn 0 1 3 4 (by omega) (by omega) (by omega))
      (hn 1 2 4 5 (by omega) (by omega) (by omega)) (hn 0 2 3 5 (by omega) (by omega) (by omega))
  have f2 : i2 = true := by
    by_contra h2
    have hn : ∀ m n p q, m < n → n < p → p < q → ¬ R (pt ν m q) (pt ν n p) :=
      fun m n p q h1' h2' h3 hR => h2 ((H m n p q h1' h2' h3).2.2.1.1 hR)
    exact htri (pt ν 0 5) (pt ν 1 4) (pt ν 2 3) (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega))
      (hne _ _ _ _ (by omega)) (hn 0 1 4 5 (by omega) (by omega) (by omega))
      (hn 1 2 3 4 (by omega) (by omega) (by omega)) (hn 0 2 3 5 (by omega) (by omega) (by omega))
  have f3 : i3 = true := by
    by_contra h3
    have hn : ∀ m n p, m < n → n < p → ¬ R (pt ν m n) (pt ν m p) :=
      fun m n p h1' h2' hR => h3 ((H m n p (p + 1) h1' h2' (by omega)).2.2.2.1 hR)
    exact htri (pt ν 0 1) (pt ν 0 2) (pt ν 0 3) (hne _ _ _ _ (by omega)) (hne _ _ _ _ (by omega))
      (hne _ _ _ _ (by omega)) (hn 0 1 2 (by omega) (by omega)) (hn 0 2 3 (by omega) (by omega))
      (hn 0 1 3 (by omega) (by omega))
  have R0 : ∀ m n p q, m < n → n < p → p < q → R (pt ν m n) (pt ν p q) :=
    fun m n p q h1 h2 h3 => (H m n p q h1 h2 h3).1.2 f0
  have R1 : ∀ m n p q, m < n → n < p → p < q → R (pt ν m p) (pt ν n q) :=
    fun m n p q h1 h2 h3 => (H m n p q h1 h2 h3).2.1.2 f1
  have R2 : ∀ m n p q, m < n → n < p → p < q → R (pt ν m q) (pt ν n p) :=
    fun m n p q h1 h2 h3 => (H m n p q h1 h2 h3).2.2.1.2 f2
  have R3 : ∀ m n p, m < n → n < p → R (pt ν m n) (pt ν m p) :=
    fun m n p h1 h2 => (H m n p (p + 1) h1 h2 (by omega)).2.2.2.2 f3
  -- the copy of `ℕ ×ₗ ℕ`
  let e : ℕ → ℕ → ℕ := fun i j => 2 * Nat.pair i j + 1
  have he_gt : ∀ i j, 2 * i < e i j := fun i j => by
    have := Nat.left_le_pair i j
    simp only [e]; omega
  have he_inj : ∀ i j i' j', e i j = e i' j' → i = i' ∧ j = j' := fun i j i' j' h =>
    Nat.pair_eq_pair.1 (by simp only [e] at h; omega)
  have he_lt : ∀ i j j', j < j' → e i j < e i j' := fun i j j' h => by
    have := Nat.pair_lt_pair_right i h
    simp only [e]; omega
  refine ⟨fun u => pt ν (2 * (ofLex u).1) (e (ofLex u).1 (ofLex u).2), ?_, ?_⟩
  · intro u v huv
    rw [Prod.Lex.lt_iff] at huv
    show toLex (ν (2 * (ofLex u).1), ν (e (ofLex u).1 (ofLex u).2)) <
      toLex (ν (2 * (ofLex v).1), ν (e (ofLex v).1 (ofLex v).2))
    rw [Prod.Lex.toLex_lt_toLex]
    rcases huv with h | ⟨h1, h2⟩
    · left
      exact hν (show 2 * (ofLex u).1 < 2 * (ofLex v).1 by omega)
    · right
      refine ⟨?_, ?_⟩
      · show ν (2 * (ofLex u).1) = ν (2 * (ofLex v).1)
        rw [h1]
      · show ν (e (ofLex u).1 (ofLex u).2) < ν (e (ofLex v).1 (ofLex v).2)
        rw [h1]
        exact hν (he_lt _ _ _ h2)
  · have key : ∀ u v : ℕ ×ₗ ℕ, u < v →
        R (pt ν (2 * (ofLex u).1) (e (ofLex u).1 (ofLex u).2))
          (pt ν (2 * (ofLex v).1) (e (ofLex v).1 (ofLex v).2)) := by
      intro u v huv
      rw [Prod.Lex.lt_iff] at huv
      generalize ofLex u = uu at huv ⊢
      generalize ofLex v = vv at huv ⊢
      obtain ⟨i, j⟩ := uu
      obtain ⟨i', j'⟩ := vv
      simp only at huv ⊢
      rcases huv with h | ⟨rfl, h⟩
      · have hm : 2 * i < 2 * i' := by omega
        have h1 := he_gt i j
        have h2 := he_gt i' j'
        have h3 : e i j ≠ 2 * i' := by simp only [e]; omega
        have h4 : e i j ≠ e i' j' := fun h' => absurd (he_inj _ _ _ _ h').1 (by omega)
        rcases lt_or_gt_of_ne h3 with h5 | h5
        · exact R0 _ _ _ _ h1 h5 h2
        · rcases lt_or_gt_of_ne h4 with h6 | h6
          · exact R1 _ _ _ _ hm h5 h6
          · exact R2 _ _ _ _ hm h2 h6
      · exact R3 _ _ _ (he_gt i j) (he_lt _ _ _ h)
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · exact key u v h
    · exact hsymm _ _ (key v u h)


open Cardinal Ordinal in
lemma type_lex_nat_nat : typeLT (ℕ ×ₗ ℕ) = ω * ω := by
  have := Ordinal.type_prod_lex (· < · : ℕ → ℕ → Prop) (· < · : ℕ → ℕ → Prop)
  rw [type_nat_lt] at this
  exact this

open Cardinal Ordinal in
/-- A well-order of type `ω ^ 2` (in any universe) is order isomorphic to `ℕ ×ₗ ℕ`. -/
lemma exists_iso_lex {W : Type u} [LinearOrder W] [WellFoundedLT W] (h : typeLT W = ω ^ 2) :
    Nonempty (W ≃o ULift.{u} (ℕ ×ₗ ℕ)) := by
  have h2 : typeLT W = typeLT (ULift.{u} (ℕ ×ₗ ℕ)) := by
    rw [h, type_lt_ulift, type_lex_nat_nat, Ordinal.lift_mul, Ordinal.lift_omega0, pow_two]
  obtain ⟨f⟩ := Ordinal.type_eq.1 h2
  exact ⟨OrderIso.ofRelIsoLT f⟩


end Erdos592Sol

open Cardinal Ordinal in
theorem solution : Erdos592.OrdinalCardinalRamsey.{u} (ω ^ 2) (ω ^ 2) 3 := by
  intro red blue hc
  by_contra hno
  push Not at hno
  obtain ⟨hr, hb⟩ := hno
  obtain ⟨iso⟩ := Erdos592Sol.exists_iso_lex (W := (ω ^ 2 : Ordinal.{u}).ToType)
    (type_toType _)
  let R : ℕ ×ₗ ℕ → ℕ ×ₗ ℕ → Prop := fun x y =>
    red.Adj (iso.symm (ULift.up x)) (iso.symm (ULift.up y))
  have hdist : ∀ x y : ℕ ×ₗ ℕ, x ≠ y → iso.symm (ULift.up x) ≠ iso.symm (ULift.up y) := by
    intro x y hxy h
    exact hxy (by simpa using iso.symm.injective h)
  have hblue : ∀ x y : ℕ ×ₗ ℕ, x ≠ y → ¬ R x y → blue.Adj (iso.symm (ULift.up x)) (iso.symm (ULift.up y)) := by
    intro x y hxy hR
    have h1 : (red ⊔ blue).Adj (iso.symm (ULift.up x)) (iso.symm (ULift.up y)) := by
      rw [hc.sup_eq_top]
      exact (SimpleGraph.top_adj _ _).2 (hdist x y hxy)
    rcases (SimpleGraph.sup_adj _ _ _ _).1 h1 with h | h
    · exact absurd h hR
    · exact h
  have htri : ∀ x y z : ℕ ×ₗ ℕ, x ≠ y → y ≠ z → x ≠ z → ¬ R x y → ¬ R y z → ¬ R x z → False := by
    intro x y z hxy hyz hxz h1 h2 h3
    refine hb {iso.symm (ULift.up x), iso.symm (ULift.up y), iso.symm (ULift.up z)} ?_ ?_
    · intro a ha b hb' hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb'
      rcases ha with rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl
      all_goals first
        | exact absurd rfl hab
        | exact hblue _ _ hxy h1
        | exact (hblue _ _ hxy h1).symm
        | exact hblue _ _ hyz h2
        | exact (hblue _ _ hyz h2).symm
        | exact hblue _ _ hxz h3
        | exact (hblue _ _ hxz h3).symm
    · rw [Cardinal.mk_insert, Cardinal.mk_insert, Cardinal.mk_singleton]
      · norm_num
      · simpa using hdist y z hyz
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hdist x y hxy, hdist x z hxz⟩
  obtain ⟨φ, hφ, hred⟩ := Erdos592Sol.specker_core R
    (fun x y h => h.symm) htri
  let ψ : ULift.{u} (ℕ ×ₗ ℕ) ↪o (ω ^ 2 : Ordinal.{u}).ToType :=
    OrderEmbedding.ofStrictMono (fun x => iso.symm (ULift.up (φ x.down)))
      (fun x y h => iso.symm.strictMono (by exact hφ h))
  refine hr (Set.range ψ) ?_ ?_
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    refine hred x.down y.down ?_
    intro h
    exact hxy (by rw [show x = y from ULift.ext _ _ h])
  · rw [← OrderIso.ordinalType_congr ψ.orderIso, type_lt_ulift, Erdos592Sol.type_lex_nat_nat, Ordinal.lift_mul,
      Ordinal.lift_omega0, pow_two]
