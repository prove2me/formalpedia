-- Prove2me | solution 1 for FatFlat.Hereditary.lemma_6_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T08:11:52.895557+00:00
-- url     : https://prove2.me/submissions/a1fd1a6d-c942-4e9e-a4bc-e8de0308d744

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Classes

section
set_option autoImplicit false

namespace FatFlat.Dev.L64Ramsey

/-- size bound for end-homogeneous sets -/
def gb (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => k * gb k t + 2

theorem end_hom {α : Type} [LinearOrder α] {β : Type} [Fintype β] [DecidableEq β]
    (col : α → α → β) :
    ∀ (t : ℕ) (S : Finset α), gb (Fintype.card β) t ≤ S.card →
      ∃ T ⊆ S, t ≤ T.card ∧ ∃ e : α → β, ∀ i ∈ T, ∀ j ∈ T, i < j → col i j = e i := by
  intro t
  induction t with
  | zero =>
    intro S _
    exact ⟨∅, Finset.empty_subset _, by simp, fun a => col a a, by simp⟩
  | succ t ih =>
    intro S hS
    have hne : S.Nonempty := by
      rw [← Finset.card_pos]
      simp only [gb] at hS
      omega
    set v := S.min' hne with hv
    have hvS : v ∈ S := Finset.min'_mem S hne
    have hcard : (S.erase v).card = S.card - 1 := Finset.card_erase_of_mem hvS
    have hlt : (Finset.univ : Finset β).card * gb (Fintype.card β) t < (S.erase v).card := by
      simp only [gb] at hS
      rw [Finset.card_univ, hcard]
      omega
    obtain ⟨b, -, hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S.erase v) (t := Finset.univ) (f := fun j => col v j) (fun _ _ => Finset.mem_univ _) hlt
    obtain ⟨T', hT'sub, hT'card, e', he'⟩ :=
      ih ((S.erase v).filter (fun j => col v j = b)) hb.le
    refine ⟨insert v T', ?_, ?_, fun i => if i = v then b else e' i, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hvS
      · exact Finset.mem_of_mem_erase (Finset.mem_filter.1 (hT'sub hx)).1
    · have hvT : v ∉ T' := fun h => by
        have := (Finset.mem_filter.1 (hT'sub h)).1
        simp at this
      rw [Finset.card_insert_of_notMem hvT]
      omega
    · intro i hi j hj hij
      have hmem : ∀ x ∈ T', x ∈ S ∧ x ≠ v ∧ col v x = b := fun x hx => by
        have := Finset.mem_filter.1 (hT'sub hx)
        exact ⟨Finset.mem_of_mem_erase this.1, Finset.ne_of_mem_erase this.1, this.2⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact absurd hij (lt_irrefl _)
        · simp [(hmem j hj).2.2]
      · have hiv : i ≠ v := (hmem i hi).2.1
        have hvi : v ≤ i := Finset.min'_le S i (hmem i hi).1
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact absurd (lt_of_le_of_lt hvi hij) (lt_irrefl _)
        · simp only [hiv, if_false]
          exact he' i hi j hj hij

/-- the Ramsey bound -/
def rb (k n : ℕ) : ℕ := gb k (k * n + 1)

theorem ramsey_pairs {α : Type} [LinearOrder α] {β : Type} [Fintype β]
    (col : α → α → β) (n : ℕ) (S : Finset α)
    (hS : rb (Fintype.card β) n ≤ S.card) :
    ∃ T ⊆ S, n ≤ T.card ∧ ∃ b : β, ∀ i ∈ T, ∀ j ∈ T, i < j → col i j = b := by
  classical
  obtain ⟨T, hTS, hTc, e, he⟩ := end_hom col _ S hS
  have hlt : (Finset.univ : Finset β).card * n < T.card := by
    rw [Finset.card_univ]; omega
  obtain ⟨b, -, hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := T) (t := Finset.univ) (f := e) (fun _ _ => Finset.mem_univ _) hlt
  refine ⟨T.filter (fun x => e x = b), fun x hx => hTS (Finset.mem_filter.1 hx).1, hb.le, b, ?_⟩
  intro i hi j hj hij
  have hi' := Finset.mem_filter.1 hi
  have hj' := Finset.mem_filter.1 hj
  rw [he i hi'.1 j hj'.1 hij, hi'.2]

end FatFlat.Dev.L64Ramsey
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L64Fan
open FatFlat.Hereditary

/-- abstract family of tree paths `q x 0 = o, ..., q x lam = x` -/
structure TF {V : Type} (G : SimpleGraph V) (o : V) (lam : ℕ) (T : Finset V) (q : V → ℕ → V) :
    Prop where
  zero : ∀ x ∈ T, q x 0 = o
  last : ∀ x ∈ T, q x lam = x
  inj : ∀ x ∈ T, ∀ a ≤ lam, ∀ b ≤ lam, q x a = q x b → a = b
  succ : ∀ x ∈ T, ∀ a < lam, G.Adj (q x a) (q x (a + 1))
  near : ∀ x ∈ T, ∀ y ∈ T, ∀ a ≤ lam, ∀ b ≤ lam, G.Adj (q x a) (q y b) → a ≤ b + 1
  disj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ a b, 1 ≤ a → a ≤ lam → 1 ≤ b → b ≤ lam → q x a ≠ q y b

theorem TF.mono {V : Type} {G : SimpleGraph V} {o : V} {lam : ℕ} {T T' : Finset V}
    {q : V → ℕ → V} (tf : TF G o lam T q) (h : T' ⊆ T) : TF G o lam T' q :=
  ⟨fun x hx => tf.zero x (h hx), fun x hx => tf.last x (h hx),
   fun x hx => tf.inj x (h hx), fun x hx => tf.succ x (h hx),
   fun x hx y hy => tf.near x (h hx) y (h hy),
   fun x hx y hy => tf.disj x (h hx) y (h hy)⟩

theorem TF.path_adj {V : Type} {G : SimpleGraph V} {o : V} {lam : ℕ} {T : Finset V}
    {q : V → ℕ → V} (tf : TF G o lam T q) {x : V} (hx : x ∈ T) {i j : ℕ} (hi : i ≤ lam)
    (hj : j ≤ lam) : G.Adj (q x i) (q x j) ↔ (i + 1 = j ∨ j + 1 = i) := by
  constructor
  · intro h
    have h1 := tf.near x hx x hx i hi j hj h
    have h2 := tf.near x hx x hx j hj i hi h.symm
    have h3 : i ≠ j := by
      rintro rfl
      exact G.loopless.irrefl _ h
    omega
  · rintro (rfl | rfl)
    · exact tf.succ x hx i (by omega)
    · exact (tf.succ x hx j (by omega)).symm

theorem fan_indep {V : Type} {G : SimpleGraph V} {o : V} {lam : ℕ} {T : Finset V}
    {q : V → ℕ → V} (tf : TF G o lam T q) (hlam : 1 ≤ lam) (X : Set V)
    (hX : ∀ x ∈ X, x ∈ T)
    (hno : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ a b, 1 ≤ a → a ≤ lam → 1 ≤ b → b ≤ lam →
      ¬ G.Adj (q x a) (q y b)) : HasFan G lam X := by
  refine ⟨o, fun x i => q x i.val, ?_⟩
  refine ⟨hlam, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact tf.zero x (hX x hx)
  · intro x hx
    exact tf.last x (hX x hx)
  · intro x hx i j h
    exact Fin.ext (tf.inj x (hX x hx) i.val (by omega) j.val (by omega) h)
  · intro x hx i j
    exact tf.path_adj (hX x hx) (by omega) (by omega)
  · intro x hx y hy hxy i j hi hj
    have hi' : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext h) hi
      · exact h
    have hj' : 1 ≤ j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exact absurd (Fin.ext h) hj
      · exact h
    exact tf.disj x (hX x hx) y (hX y hy) hxy _ _ hi' (by omega) hj' (by omega)
  · left
    intro x hx y hy hxy i j hi hj
    have hi' : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext h) hi
      · exact h
    have hj' : 1 ≤ j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exact absurd (Fin.ext h) hj
      · exact h
    exact hno x (hX x hx) y (hX y hy) hxy _ _ hi' (by omega) hj' (by omega)

theorem fan_rooted {V : Type} {G : SimpleGraph V} {o : V} {lam : ℕ} {T : Finset V}
    {q : V → ℕ → V} (tf : TF G o lam T q)
    (lt : V → V → Prop) (x0 : V) (hx0 : x0 ∈ T)
    (htot : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lt x y ∨ lt y x)
    (hroot : ∀ y ∈ T, y ≠ x0 → lt x0 y)
    (Cp : ℕ → ℕ → Prop)
    (hcol : ∀ x ∈ T, ∀ y ∈ T, lt x y → ∀ a b, 1 ≤ a → a ≤ lam → 1 ≤ b → b ≤ lam →
      (G.Adj (q x a) (q y b) ↔ Cp a b))
    (a h : ℕ) (ha1 : 1 ≤ a) (hah : a ≤ h) (hhl : h ≤ lam) (hCa : Cp a h)
    (hmax : ∀ a' b', 1 ≤ a' → a' ≤ lam → 1 ≤ b' → b' ≤ lam → Cp a' b' → a' ≤ h ∧ b' ≤ h)
    (X : Set V) (hX : ∀ x ∈ X, x ∈ T ∧ x ≠ x0) : HasFan G (lam - h + 1) X := by
  have suffix_adj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ∀ b b', h ≤ b → b ≤ lam → h ≤ b' → b' ≤ lam →
      (G.Adj (q x b) (q y b') ↔ (b = h ∧ b' = h ∧ Cp h h)) := by
    intro x hx y hy hxy b b' hb1 hb2 hb1' hb2'
    rcases htot x hx y hy hxy with hl | hl
    · rw [hcol x hx y hy hl b b' (by omega) hb2 (by omega) hb2']
      constructor
      · intro hc
        have := hmax b b' (by omega) hb2 (by omega) hb2' hc
        have e1 : b = h := by omega
        have e2 : b' = h := by omega
        subst e1; subst e2
        exact ⟨rfl, rfl, hc⟩
      · rintro ⟨rfl, rfl, hc⟩
        exact hc
    · rw [SimpleGraph.adj_comm, hcol y hy x hx hl b' b (by omega) hb2' (by omega) hb2]
      constructor
      · intro hc
        have := hmax b' b (by omega) hb2' (by omega) hb2 hc
        have e1 : b = h := by omega
        have e2 : b' = h := by omega
        subst e1; subst e2
        exact ⟨rfl, rfl, hc⟩
      · rintro ⟨rfl, rfl, hc⟩
        exact hc
  have root_adj : ∀ y ∈ T, y ≠ x0 → ∀ b, 1 ≤ b → b ≤ lam →
      (G.Adj (q x0 a) (q y b) ↔ Cp a b) := fun y hy hne b hb1 hb2 =>
    hcol x0 hx0 y hy (hroot y hy hne) a b ha1 (by omega) hb1 hb2
  have nz : ∀ {ℓ : ℕ} (i : Fin (ℓ + 1)), i ≠ 0 → 1 ≤ i.val := by
    intro ℓ i hi
    rcases Nat.eq_zero_or_pos i.val with h | h
    · exact absurd (Fin.ext h) hi
    · exact h
  refine ⟨q x0 a, fun x i => if i.val = 0 then q x0 a else q x (h + i.val - 1), ?_⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp
  · intro x hx
    have : (Fin.last (lam - h + 1)).val ≠ 0 := by simp
    simp only [this, if_false]
    have e : h + (Fin.last (lam - h + 1)).val - 1 = lam := by simp; omega
    rw [e]
    exact tf.last x (hX x hx).1
  · intro x hx i j hij
    obtain ⟨hxT, hxne⟩ := hX x hx
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact Fin.ext (by omega)
      · simp only [hi, hj, if_true, if_false] at hij
        exact absurd hij (tf.disj x0 hx0 x hxT (Ne.symm hxne) a _ ha1 (by omega) (by omega)
          (by have := j.isLt; omega))
    · by_cases hj : j.val = 0
      · simp only [hi, hj, if_true, if_false] at hij
        exact absurd hij.symm (tf.disj x0 hx0 x hxT (Ne.symm hxne) a _ ha1 (by omega) (by omega)
          (by have := i.isLt; omega))
      · simp only [hi, hj, if_false] at hij
        have := tf.inj x hxT _ (by have := i.isLt; omega) _ (by have := j.isLt; omega) hij
        exact Fin.ext (by omega)
  · intro x hx i j
    obtain ⟨hxT, hxne⟩ := hX x hx
    have hl := hhl
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · simp only [hi, hj, if_true]
        constructor
        · intro hc; exact absurd hc (G.loopless.irrefl _)
        · omega
      · simp only [hi, hj, if_true, if_false]
        have hjl := j.isLt
        rw [root_adj x hxT hxne _ (by omega) (by omega)]
        constructor
        · intro hc
          have := hmax a _ ha1 (by omega) (by omega) (by omega) hc
          omega
        · intro hc
          have : h + j.val - 1 = h := by omega
          rw [this]; exact hCa
    · by_cases hj : j.val = 0
      · simp only [hi, hj, if_true, if_false]
        have hil := i.isLt
        rw [SimpleGraph.adj_comm, root_adj x hxT hxne _ (by omega) (by omega)]
        constructor
        · intro hc
          have := hmax a _ ha1 (by omega) (by omega) (by omega) hc
          omega
        · intro hc
          have : h + i.val - 1 = h := by omega
          rw [this]; exact hCa
      · simp only [hi, hj, if_false]
        have hil := i.isLt
        have hjl := j.isLt
        rw [tf.path_adj hxT (by omega) (by omega)]
        omega
  · intro x hx y hy hxy i j hi hj
    have hi' : ¬ i.val = 0 := fun h => hi (Fin.ext h)
    have hj' : ¬ j.val = 0 := fun h => hj (Fin.ext h)
    have hil := i.isLt
    have hjl := j.isLt
    simp only [hi', hj', if_false]
    exact tf.disj x (hX x hx).1 y (hX y hy).1 hxy _ _ (by omega) (by omega) (by omega) (by omega)
  · by_cases hc : Cp h h
    · right
      intro x hx y hy hxy i j hi hj
      have hi' : ¬ i.val = 0 := fun h => hi (Fin.ext h)
      have hj' : ¬ j.val = 0 := fun h => hj (Fin.ext h)
      have hil := i.isLt
      have hjl := j.isLt
      simp only [hi', hj', if_false]
      rw [suffix_adj x (hX x hx).1 y (hX y hy).1 hxy _ _ (by omega) (by omega) (by omega)
        (by omega)]
      constructor
      · rintro ⟨h1, h2, -⟩
        omega
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, by omega, hc⟩
    · left
      intro x hx y hy hxy i j hi hj
      have hi' : ¬ i.val = 0 := fun h => hi (Fin.ext h)
      have hj' : ¬ j.val = 0 := fun h => hj (Fin.ext h)
      have hil := i.isLt
      have hjl := j.isLt
      simp only [hi', hj', if_false]
      rw [suffix_adj x (hX x hx).1 y (hX y hy).1 hxy _ _ (by omega) (by omega) (by omega)
        (by omega)]
      rintro ⟨-, -, h3⟩
      exact hc h3


open FatFlat.Dev.L64Ramsey in
theorem fan_of_tf {V : Type} [Fintype V] {G : SimpleGraph V} {o : V} {lam : ℕ} {T : Finset V}
    {q : V → ℕ → V} (tf : TF G o lam T q) (R : ℕ) (hlam1 : 1 ≤ lam) (hlamR : lam ≤ R)
    (m : ℕ) (hT : rb (Fintype.card (Fin (R + 1) → Fin (R + 1) → Bool)) (m + 1) ≤ T.card) :
    ∃ X' ⊆ T, X'.card = m ∧ ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ lam ∧ HasFan G ℓ (X' : Set V) := by
  classical
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let col : V → V → (Fin (R + 1) → Fin (R + 1) → Bool) := fun x y a b =>
    decide (1 ≤ a.val ∧ a.val ≤ lam ∧ 1 ≤ b.val ∧ b.val ≤ lam ∧ G.Adj (q x a.val) (q y b.val))
  obtain ⟨T', hT'T, hT'c, c0, hc0⟩ := ramsey_pairs col (m + 1) T hT
  let Cp : ℕ → ℕ → Prop := fun a b => ∃ (ha : a < R + 1) (hb : b < R + 1),
    c0 ⟨a, ha⟩ ⟨b, hb⟩ = true
  have hcol : ∀ x ∈ T', ∀ y ∈ T', x < y → ∀ a b, 1 ≤ a → a ≤ lam → 1 ≤ b → b ≤ lam →
      (G.Adj (q x a) (q y b) ↔ Cp a b) := by
    intro x hx y hy hxy a b ha1 ha2 hb1 hb2
    have hc := hc0 x hx y hy hxy
    constructor
    · intro hadj
      refine ⟨by omega, by omega, ?_⟩
      rw [← hc]
      simp [col, ha1, ha2, hb1, hb2, hadj]
    · rintro ⟨ha, hb, h⟩
      rw [← hc] at h
      have h := by simpa [col] using h
      exact h.2.2.2.2
  have tf' : TF G o lam T' q := tf.mono hT'T
  have hne : T'.Nonempty := by
    rw [← Finset.card_pos]; omega
  by_cases hnone : ∀ a b, 1 ≤ a → a ≤ lam → 1 ≤ b → b ≤ lam → ¬ Cp a b
  · obtain ⟨X', hX'T', hX'c⟩ := Finset.exists_subset_card_eq (s := T') (n := m) (by omega)
    refine ⟨X', fun x hx => hT'T (hX'T' hx), hX'c, lam, hlam1, le_refl _, ?_⟩
    refine fan_indep tf' hlam1 _ (fun x hx => hX'T' hx) ?_
    intro x hx y hy hxy a b ha1 ha2 hb1 hb2 hadj
    rcases lt_or_gt_of_ne hxy with hl | hl
    · exact hnone a b ha1 ha2 hb1 hb2 ((hcol x hx y hy hl a b ha1 ha2 hb1 hb2).1 hadj)
    · exact hnone b a hb1 hb2 ha1 ha2 ((hcol y hy x hx hl b a hb1 hb2 ha1 ha2).1 hadj.symm)
  · push_neg at hnone
    obtain ⟨a1, b1, ha1, ha1', hb1, hb1', hC1⟩ := hnone
    let Q : Finset (ℕ × ℕ) :=
      (Finset.Icc 1 lam ×ˢ Finset.Icc 1 lam).filter (fun p => Cp p.1 p.2)
    have hQne : Q.Nonempty := ⟨(a1, b1), by simp [Q, ha1, ha1', hb1, hb1', hC1]⟩
    obtain ⟨⟨a0, b0⟩, hQ0, hQmax⟩ := Finset.exists_max_image Q (fun p => max p.1 p.2) hQne
    simp only [Q, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hQ0
    obtain ⟨⟨⟨ha0, ha0'⟩, hb0, hb0'⟩, hC0⟩ := hQ0
    have hmax : ∀ a' b', 1 ≤ a' → a' ≤ lam → 1 ≤ b' → b' ≤ lam → Cp a' b' →
        a' ≤ max a0 b0 ∧ b' ≤ max a0 b0 := by
      intro a' b' h1 h2 h3 h4 hc
      have := hQmax (a', b') (by simp [Q, h1, h2, h3, h4, hc])
      simp only at this
      exact ⟨le_trans (le_max_left _ _) this, le_trans (le_max_right _ _) this⟩
    have hcard : m ≤ (T'.erase (T'.min' hne)).card := by
      rw [Finset.card_erase_of_mem (Finset.min'_mem _ _)]; omega
    rcases le_total a0 b0 with hab | hab
    · -- (a0, b0) with b0 maximal : root = min
      have hh : max a0 b0 = b0 := max_eq_right hab
      obtain ⟨X', hX'sub, hX'c⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨X', fun x hx => hT'T (Finset.mem_of_mem_erase (hX'sub hx)), hX'c,
        lam - b0 + 1, by omega, by omega, ?_⟩
      refine fan_rooted tf' (· < ·) (T'.min' hne) (Finset.min'_mem _ _)
        (fun x hx y hy hxy => lt_or_gt_of_ne hxy) ?_ Cp hcol a0 b0 ha0 hab hb0' hC0 ?_ _ ?_
      · intro y hy hne'
        exact lt_of_le_of_ne (Finset.min'_le _ _ hy) (Ne.symm hne')
      · intro a' b' h1 h2 h3 h4 hc
        rw [hh] at hmax
        exact hmax a' b' h1 h2 h3 h4 hc
      · intro x hx
        exact ⟨Finset.mem_of_mem_erase (hX'sub hx), Finset.ne_of_mem_erase (hX'sub hx)⟩
    · have hh : max a0 b0 = a0 := max_eq_left hab
      have hcard' : m ≤ (T'.erase (T'.max' hne)).card := by
        rw [Finset.card_erase_of_mem (Finset.max'_mem _ _)]; omega
      obtain ⟨X', hX'sub, hX'c⟩ := Finset.exists_subset_card_eq hcard'
      refine ⟨X', fun x hx => hT'T (Finset.mem_of_mem_erase (hX'sub hx)), hX'c,
        lam - a0 + 1, by omega, by omega, ?_⟩
      refine fan_rooted tf' (· > ·) (T'.max' hne) (Finset.max'_mem _ _)
        (fun x hx y hy hxy => (lt_or_gt_of_ne hxy).symm) ?_ (fun a b => Cp b a) ?_ b0 a0 hb0 hab
        ha0' hC0 ?_ _ ?_
      · intro y hy hne'
        exact lt_of_le_of_ne (Finset.le_max' _ _ hy) hne'
      · intro x hx y hy hxy a b h1 h2 h3 h4
        rw [SimpleGraph.adj_comm]
        exact hcol y hy x hx hxy b a h3 h4 h1 h2
      · intro a' b' h1 h2 h3 h4 hc
        rw [hh] at hmax
        exact (hmax b' a' h3 h4 h1 h2 hc).symm
      · intro x hx
        exact ⟨Finset.mem_of_mem_erase (hX'sub hx), Finset.ne_of_mem_erase (hX'sub hx)⟩

end FatFlat.Dev.L64Fan
end

section
set_option autoImplicit false

namespace FatFlat.Dev.L64
open FatFlat.Hereditary FatFlat.Dev.L64Fan FatFlat.Dev.L64Ramsey

section bfs
variable {V : Type} (G : SimpleGraph V) (o : V)

/-- `Lv v n`: the vertex `v` is at distance exactly `n` from `o`. -/
def Lv (v : V) (n : ℕ) : Prop := G.edist o v = (n : ℕ∞)

theorem exists_par {v : V} (hv : v ≠ o) (hne : G.edist o v ≠ ⊤) :
    ∃ u, G.Adj u v ∧ G.edist o u + 1 = G.edist o v := by
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hrev := p.reverse
  generalize hpr : p.reverse = pr
  cases pr with
  | nil => exact absurd rfl hv
  | @cons _ u _ hadj q =>
    have hlen : q.length + 1 = p.length := by
      have := congrArg SimpleGraph.Walk.length hpr
      simp at this
      omega
    refine ⟨u, hadj.symm, ?_⟩
    have h1 : G.edist o u ≤ q.length := by
      rw [SimpleGraph.edist_comm]; exact SimpleGraph.edist_le q
    have h2 : G.edist o v ≤ G.edist o u + 1 := by
      calc G.edist o v ≤ G.edist o u + G.edist u v := SimpleGraph.edist_triangle
        _ = G.edist o u + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj.symm]
    apply le_antisymm
    · exact h2.trans (le_refl _) |> fun h => by
        calc G.edist o u + 1 ≤ (q.length : ℕ∞) + 1 := by gcongr
          _ = ((q.length + 1 : ℕ) : ℕ∞) := by push_cast; rfl
          _ = G.edist o v := by rw [hlen, hp]
    · exact h2

open Classical in
noncomputable def par (v : V) : V :=
  if h : v ≠ o ∧ G.edist o v ≠ ⊤ then Classical.choose (exists_par G o h.1 h.2) else v

theorem par_lv {v : V} {n : ℕ} (h : Lv G o v (n + 1)) : G.Adj (par G o v) v ∧ Lv G o (par G o v) n := by
  have hv : v ≠ o := by
    rintro rfl
    unfold Lv at h
    rw [SimpleGraph.edist_self] at h
    have h' : (0 : ℕ) = n + 1 := by exact_mod_cast h
    omega
  have hne : G.edist o v ≠ ⊤ := by
    unfold Lv at h; rw [h]; exact ENat.natCast_ne_top _
  have hh : v ≠ o ∧ G.edist o v ≠ ⊤ := ⟨hv, hne⟩
  have hpar : par G o v = Classical.choose (exists_par G o hv hne) := by
    unfold par; rw [dif_pos hh]
  have spec := Classical.choose_spec (exists_par G o hv hne)
  rw [← hpar] at spec
  refine ⟨spec.1, ?_⟩
  unfold Lv at h ⊢
  have h2 := spec.2
  rw [h] at h2
  have hne' : G.edist o (par G o v) ≠ ⊤ := by
    intro h3; rw [h3] at h2
    exact ENat.natCast_ne_top (n + 1) (by exact_mod_cast h2.symm)
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hne'
  rw [← he] at h2 ⊢
  have : e + 1 = n + 1 := by exact_mod_cast h2
  have : e = n := by omega
  rw [this]

theorem iter_lv {x : V} {d : ℕ} (h : Lv G o x d) :
    ∀ k ≤ d, Lv G o ((par G o)^[k] x) (d - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using h
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : d - k = (d - (k + 1)) + 1 := by omega
    rw [h2] at h1
    rw [Function.iterate_succ_apply']
    exact (par_lv G o h1).2

theorem lv_unique {v : V} {a b : ℕ} (ha : Lv G o v a) (hb : Lv G o v b) : a = b := by
  unfold Lv at ha hb
  rw [ha] at hb
  exact_mod_cast hb

theorem adj_lv {u v : V} {a b : ℕ} (hadj : G.Adj u v) (hu : Lv G o u a) (hv : Lv G o v b) :
    b ≤ a + 1 := by
  unfold Lv at hu hv
  have : G.edist o v ≤ G.edist o u + 1 := by
    calc G.edist o v ≤ G.edist o u + G.edist u v := SimpleGraph.edist_triangle
      _ = G.edist o u + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]
  rw [hu, hv] at this
  exact_mod_cast this

theorem edist_iter {x : V} {d : ℕ} (h : Lv G o x d) :
    ∀ k ≤ d, G.edist ((par G o)^[k] x) x ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := iter_lv G o h k (by omega)
    have h3 : d - k = (d - (k + 1)) + 1 := by omega
    rw [h3] at h2
    have hadj := (par_lv G o h2).1
    rw [Function.iterate_succ_apply']
    calc G.edist (par G o ((par G o)^[k] x)) x
        ≤ G.edist (par G o ((par G o)^[k] x)) ((par G o)^[k] x) + G.edist ((par G o)^[k] x) x :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + k := by
          rw [SimpleGraph.edist_eq_one_iff_adj.2 hadj]
          gcongr
      _ = ((k + 1 : ℕ) : ℕ∞) := by push_cast; ring

theorem tf_of_levels (T : Finset V) (lam : ℕ) (hlam : 1 ≤ lam)
    (hT : ∀ x ∈ T, Lv G o x lam)
    (hf : ∀ x ∈ T, ∀ y ∈ T, (par G o)^[lam - 1] x = (par G o)^[lam - 1] y → x = y) :
    TF G o lam T (fun x a => (par G o)^[lam - a] x) := by
  have hlev : ∀ x ∈ T, ∀ a ≤ lam, Lv G o ((par G o)^[lam - a] x) a := by
    intro x hx a ha
    have := iter_lv G o (hT x hx) (lam - a) (by omega)
    have e : lam - (lam - a) = a := by omega
    rwa [e] at this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hlev x hx 0 (by omega)
    unfold Lv at this
    simp only [Nat.cast_zero, SimpleGraph.edist_eq_zero_iff] at this
    exact this.symm
  · intro x hx
    simp
  · intro x hx a ha b hb hab
    exact lv_unique G o (hlev x hx a ha) (hab ▸ hlev x hx b hb)
  · intro x hx a ha
    have h1 := hlev x hx (a + 1) (by omega)
    have h2 : lam - a = (lam - (a + 1)) + 1 := by omega
    show G.Adj ((par G o)^[lam - a] x) ((par G o)^[lam - (a + 1)] x)
    rw [h2, Function.iterate_succ_apply']
    exact (par_lv G o h1).1
  · intro x hx y hy a ha b hb hadj
    exact adj_lv G o hadj.symm (hlev y hy b hb) (hlev x hx a ha)
  · intro x hx y hy hxy a b ha1 ha2 hb1 hb2 heq
    have hab : a = b := lv_unique G o (hlev x hx a ha2) (heq ▸ hlev y hy b hb2)
    subst hab
    apply hxy
    apply hf x hx y hy
    have e : lam - 1 = (a - 1) + (lam - a) := by omega
    rw [e, Function.iterate_add_apply, Function.iterate_add_apply]
    exact congrArg _ heq

end bfs

/-- the statement for a fixed `r` -/
def Stmt (r : ℕ) : Prop :=
  ∃ F : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (o : V)
    (m : ℕ) (X : Finset V), F m ≤ X.card → (∀ x ∈ X, G.edist o x ≤ r) →
    ∃ X' : Finset V, X' ⊆ X ∧ X'.card = m ∧
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ r ∧ HasFan G ℓ (X' : Set V)

theorem stmt_zero : Stmt 0 := by
  refine ⟨fun _ => 2, ?_⟩
  intro V _ G o m X hX hd
  have hX : 2 ≤ X.card := hX
  exfalso
  have hsub : X ⊆ {o} := by
    intro x hx
    have := hd x hx
    simp only [Nat.cast_zero, nonpos_iff_eq_zero, SimpleGraph.edist_eq_zero_iff] at this
    simp [this.symm]
  have := Finset.card_le_card hsub
  simp at this
  omega

theorem stmt_succ (r : ℕ) (hr : Stmt r) : Stmt (r + 1) := by
  obtain ⟨F, hF⟩ := hr
  classical
  refine ⟨fun m => ((r + 1) * rb (Fintype.card (Fin (r + 1 + 1) → Fin (r + 1 + 1) → Bool)) (m + 1))
    * F m + 2, ?_⟩
  intro V _ G o m X hX hd
  have hX : (r + 1) * rb (Fintype.card (Fin (r + 1 + 1) → Fin (r + 1 + 1) → Bool)) (m + 1)
    * F m + 2 ≤ X.card := hX
  set R := r + 1 with hR
  set W := rb (Fintype.card (Fin (R + 1) → Fin (R + 1) → Bool)) (m + 1) with hW
  set n := F m with hn
  set X0 := X.erase o with hX0
  have hcard : R * W * n < X0.card := by
    have := Finset.pred_card_le_card_erase (s := X) (a := o)
    rw [← hX0] at this
    omega
  have hX0X : X0 ⊆ X := Finset.erase_subset _ _
  let dd : V → ℕ := fun x => (G.edist o x).toNat
  have hX0lev : ∀ x ∈ X0, 1 ≤ dd x ∧ dd x ≤ R ∧ Lv G o x (dd x) := by
    intro x hx
    show 1 ≤ (G.edist o x).toNat ∧ (G.edist o x).toNat ≤ R ∧ Lv G o x (G.edist o x).toNat
    have hxo : x ≠ o := Finset.ne_of_mem_erase hx
    have hdx := hd x (hX0X hx)
    have hnt : G.edist o x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hdx
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 hnt
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hxo
      have : G.edist o x = 0 := by rw [← he]; rfl
      exact (SimpleGraph.edist_eq_zero_iff.1 this).symm
    rw [← he] at hdx ⊢
    simp only [ENat.toNat_natCast]
    refine ⟨by omega, ?_, ?_⟩
    · exact_mod_cast hdx
    · unfold Lv; rw [he]
  let f : V → V := fun x => (par G o)^[dd x - 1] x
  set I := X0.image f with hI
  by_cases hA : ∃ s ∈ I, n < (X0.filter (fun x => f x = s)).card
  · obtain ⟨s, -, hs⟩ := hA
    obtain ⟨X', hX'sub, hX'c, ℓ, hl1, hl2, hfan⟩ := hF V G s m (X0.filter (fun x => f x = s)) hs.le
      (by
        intro x hx
        obtain ⟨hxX0, hfx⟩ := Finset.mem_filter.1 hx
        obtain ⟨h1, h2, h3⟩ := hX0lev x hxX0
        have := edist_iter G o h3 (dd x - 1) (by omega)
        have h4 : f x = s := hfx
        rw [← h4]
        refine this.trans ?_
        exact_mod_cast (by omega : dd x - 1 ≤ r))
    exact ⟨X', fun x hx => hX0X (Finset.mem_filter.1 (hX'sub hx)).1, hX'c, ℓ, hl1, by omega, hfan⟩
  · push Not at hA
    have hIc : R * W < I.card := by
      by_contra hcon
      have h1 : X0.card ≤ n * I.card := Finset.card_le_mul_card_image X0 n hA
      have h2 : n * I.card ≤ n * (R * W) := Nat.mul_le_mul_left _ (by omega)
      have h4 := lt_of_lt_of_le hcard (h1.trans h2)
      rw [Nat.mul_comm n (R * W)] at h4
      exact lt_irrefl _ h4
    have hrep : ∀ s ∈ I, ∃ x ∈ X0, f x = s := fun s hs => Finset.mem_image.1 hs
    have hVne : Nonempty V := ⟨o⟩
    choose! rep hrepX hrepf using hrep
    have hmaps : ∀ s ∈ I, dd (rep s) ∈ Finset.Icc 1 R := by
      intro s hs
      obtain ⟨h1, h2, -⟩ := hX0lev _ (hrepX s hs)
      simpa [dd] using ⟨h1, h2⟩
    have hlt : (Finset.Icc 1 R).card * W < I.card := by simpa using hIc
    obtain ⟨lam, hlamI, hlamc⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt
    set J := I.filter (fun s => dd (rep s) = lam) with hJ
    have hlam := Finset.mem_Icc.1 hlamI
    have hinj : Set.InjOn rep (J : Set V) := by
      intro s hs s' hs' h
      have h1 := hrepf s (Finset.mem_filter.1 hs).1
      have h2 := hrepf s' (Finset.mem_filter.1 hs').1
      rw [← h1, ← h2]
      exact congrArg f h
    set T0 := J.image rep with hT0
    have hT0c : W ≤ T0.card := by
      rw [Finset.card_image_of_injOn hinj]
      exact hlamc.le
    have hT0mem : ∀ x ∈ T0, x ∈ X0 ∧ dd x = lam ∧ ∃ s ∈ J, rep s = x ∧ f x = s := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hx
      have hsJ := Finset.mem_filter.1 hs
      exact ⟨hrepX s hsJ.1, hsJ.2, s, hs, rfl, hrepf s hsJ.1⟩
    have tf := tf_of_levels G o T0 lam hlam.1
      (fun x hx => by
        obtain ⟨h1, h2, -⟩ := hT0mem x hx
        have := (hX0lev x h1).2.2
        rwa [h2] at this)
      (fun x hx y hy hxy => by
        obtain ⟨-, hx2, s, hs, hsx, hfx⟩ := hT0mem x hx
        obtain ⟨-, hy2, s', hs', hsy, hfy⟩ := hT0mem y hy
        have e1 : f x = (par G o)^[lam - 1] x := by simp only [f]; rw [hx2]
        have e2 : f y = (par G o)^[lam - 1] y := by simp only [f]; rw [hy2]
        have : f x = f y := by rw [e1, e2]; exact hxy
        rw [hfx, hfy] at this
        rw [← hsx, ← hsy, this])
    obtain ⟨X', hX'T, hX'c, ℓ, hl1, hl2, hfan⟩ :=
      fan_of_tf tf R hlam.1 hlam.2 m (by rw [← hW]; exact hT0c)
    exact ⟨X', fun x hx => hX0X (hT0mem x (hX'T hx)).1, hX'c, ℓ, hl1, by omega, hfan⟩

theorem stmt_all (r : ℕ) : Stmt r := by
  induction r with
  | zero => exact stmt_zero
  | succ r ih => exact stmt_succ r ih

end FatFlat.Dev.L64

namespace FatFlat.Hereditary
open FatFlat.Dev.L64 in
theorem chk_lemma_6_4 (r : ℕ) : ∃ F : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (o : V)
    (m : ℕ) (X : Finset V), F m ≤ X.card → (∀ x ∈ X, G.edist o x ≤ r) →
    ∃ X' : Finset V, X' ⊆ X ∧ X'.card = m ∧
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ r ∧ HasFan G ℓ (X' : Set V) := stmt_all r

end FatFlat.Hereditary
end

theorem solution : type_of% @FatFlat.Hereditary.chk_lemma_6_4 := @FatFlat.Hereditary.chk_lemma_6_4
