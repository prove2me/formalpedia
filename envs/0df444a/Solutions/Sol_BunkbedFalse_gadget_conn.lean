-- Prove2me | solution 1 for BunkbedFalse.gadget_conn
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:30:25.82336+00:00
-- url     : https://prove2.me/submissions/fa79ce13-94a6-4eac-a862-f963af5db208

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset
open Fin.NatCast

namespace L51

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Weight basics -/

private lemma weight_insert_notMem {E S : Finset (Sym2 V)} {e : Sym2 V}
    (hE : e ∉ E) (hS : S ⊆ E) (w : Sym2 V → ℚ) :
    weight (insert e E) w S = (1 - w e) * weight E w S := by
  have hes : e ∉ S := fun h => hE (hS h)
  have : insert e E \ S = insert e (E \ S) := by
    rw [Finset.insert_sdiff_of_notMem _ hes]
  rw [weight, weight, this, Finset.prod_insert (by simp [hE])]
  ring

private lemma weight_insert_mem {E S : Finset (Sym2 V)} {e : Sym2 V}
    (hE : e ∉ E) (hS : S ⊆ E) (w : Sym2 V → ℚ) :
    weight (insert e E) w (insert e S) = w e * weight E w S := by
  have hes : e ∉ S := fun h => hE (hS h)
  have h2 : insert e E \ insert e S = E \ S := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1) h2
      · exact ⟨h1, fun h => h2 (Or.inr h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, by push_neg; exact ⟨fun h => hE (h ▸ h1), h2⟩⟩
  rw [weight, weight, h2, Finset.prod_insert hes]
  ring

private lemma sum_weight (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) :
    ∑ S ∈ E.powerset, weight E w S = 1 := by
  have := Finset.prod_add w (fun e => 1 - w e) E
  simp only [add_sub_cancel] at this
  rw [Finset.prod_const_one] at this
  exact this.symm

/-! ### Reachability basics -/

open SimpleGraph in
private lemma reach_map {G H : SimpleGraph V} (φ : V → V)
    (hφ : ∀ u v : V, G.Adj u v → H.Adj (φ u) (φ v) ∨ φ u = φ v) {a b : V}
    (h : G.Reachable a b) : H.Reachable (φ a) (φ b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj q ih =>
      rcases hφ _ _ hadj with h1 | h1
      · exact h1.reachable.trans ih
      · rw [h1]; exact ih

private lemma adj_ofEdges {S : Finset (Sym2 V)} {u v : V} :
    (ofEdges S).Adj u v ↔ s(u, v) ∈ S ∧ u ≠ v := by
  simp [ofEdges, SimpleGraph.fromEdgeSet_adj]

/-- If `y` lies in no open edge, nothing distinct from `y` reaches it. -/
private lemma not_reach_isolated {S : Finset (Sym2 V)} {a y : V} (hay : a ≠ y)
    (hiso : ∀ e ∈ S, y ∉ e) : ¬ (ofEdges S).Reachable a y := by
  intro h
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => exact hay rfl
  | cons hadj q =>
      rw [adj_ofEdges] at hadj
      exact hiso _ hadj.1 (by simp)

private lemma ofEdges_mono {S T : Finset (Sym2 V)} (h : S ⊆ T) :
    ofEdges S ≤ ofEdges T := by
  intro u v huv
  rw [adj_ofEdges] at huv ⊢
  exact ⟨h huv.1, huv.2⟩

/-- Adding the single pendant edge `s(x,y)` at the otherwise isolated vertex `y`:
reaching `y` becomes equivalent to reaching `x`. -/
private lemma reach_pendant {E S : Finset (Sym2 V)} {a x y : V}
    (hxy : x ≠ y) (hay : a ≠ y) (hiso : ∀ e ∈ E, y ∉ e) (hS : S ⊆ E) :
    (ofEdges (insert s(x, y) S)).Reachable a y ↔ (ofEdges S).Reachable a x := by
  have hisoS : ∀ e ∈ S, y ∉ e := fun e he => hiso e (hS he)
  constructor
  · intro h
    have hmap := reach_map (G := ofEdges (insert s(x, y) S)) (H := ofEdges S)
      (φ := fun v => if v = y then x else v) ?_ h
    · simpa [hay, hxy] using hmap
    · intro u v huv
      rw [adj_ofEdges, Finset.mem_insert] at huv
      obtain ⟨hmem, hne⟩ := huv
      rcases hmem with heq | hmem
      · right
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst hu; subst hv; simp [hxy]
        · subst hu; subst hv; simp [hxy]
      · left
        have hu : u ≠ y := fun h => hisoS _ hmem (by rw [h]; simp)
        have hv : v ≠ y := fun h => hisoS _ hmem (by rw [h]; simp)
        simp only [hu, hv, if_false]
        rw [adj_ofEdges]
        exact ⟨hmem, hne⟩
  · intro h
    have h1 : (ofEdges (insert s(x, y) S)).Reachable a x :=
      h.mono (ofEdges_mono (Finset.subset_insert _ _))
    have h2 : (ofEdges (insert s(x, y) S)).Adj x y := by
      rw [adj_ofEdges]
      exact ⟨Finset.mem_insert_self _ _, hxy⟩
    exact h1.trans h2.reachable

/-! ### The conditioning step -/

/-- Conditioning on the two edges at a pendant-plus-spoke vertex `y`. -/
private lemma probOf_pendant (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a x y : V)
    (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y) (hiso : ∀ e ∈ E, y ∉ e) :
    probOf (insert s(a, y) (insert s(x, y) E)) w
        (fun S => (ofEdges S).Reachable a y)
      = w s(a, y) + (1 - w s(a, y)) * w s(x, y) *
          probOf E w (fun S => (ofEdges S).Reachable a x) := by
  have he2 : s(x, y) ∉ E := fun h => hiso _ h (by simp)
  have hne12 : s(a, y) ≠ s(x, y) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hax h1
    · exact hay h1
  have he1 : s(a, y) ∉ insert s(x, y) E := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hne12, fun h => hiso _ h (by simp)⟩
  -- term-by-term facts
  have hsubI : ∀ S : Finset (Sym2 V), S ⊆ E → insert s(x, y) S ⊆ insert s(x, y) E := by
    intro S hS
    exact Finset.insert_subset_insert _ hS
  have hA : ∑ S ∈ E.powerset, (if (ofEdges S).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w S else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro S hS
    rw [Finset.mem_powerset] at hS
    exact if_neg (not_reach_isolated hay (fun e he => hiso e (hS he)))
  have hB : ∑ S ∈ E.powerset, (if (ofEdges (insert s(x, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(x, y) S) else 0)
      = (1 - w s(a, y)) * w s(x, y) *
          probOf E w (fun S => (ofEdges S).Reachable a x) := by
    rw [probOf, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hw : weight (insert s(a, y) (insert s(x, y) E)) w (insert s(x, y) S)
        = (1 - w s(a, y)) * (w s(x, y) * weight E w S) := by
      rw [weight_insert_notMem he1 (hsubI S hS) w, weight_insert_mem he2 hS w]
    by_cases hr : (ofEdges S).Reachable a x
    · rw [if_pos ((reach_pendant hxy hay hiso hS).2 hr), if_pos hr, hw]; ring
    · rw [if_neg (fun h => hr ((reach_pendant hxy hay hiso hS).1 h)), if_neg hr]; ring
  have hCD : ∀ S : Finset (Sym2 V), S ⊆ E →
      (ofEdges (insert s(a, y) S)).Reachable a y ∧
      (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y := by
    intro S _
    constructor
    · exact (show (ofEdges (insert s(a, y) S)).Adj a y by
        rw [adj_ofEdges]; exact ⟨Finset.mem_insert_self _ _, hay⟩).reachable
    · exact (show (ofEdges (insert s(a, y) (insert s(x, y) S))).Adj a y by
        rw [adj_ofEdges]; exact ⟨Finset.mem_insert_self _ _, hay⟩).reachable
  have hC : ∑ S ∈ E.powerset, (if (ofEdges (insert s(a, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) S) else 0)
      = w s(a, y) * (1 - w s(x, y)) := by
    have : ∀ S ∈ E.powerset, (if (ofEdges (insert s(a, y) S)).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) S) else 0)
        = w s(a, y) * (1 - w s(x, y)) * weight E w S := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      rw [if_pos (hCD S hS).1,
        weight_insert_mem he1 (hS.trans (Finset.subset_insert _ _)) w,
        weight_insert_notMem he2 hS w]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_weight, mul_one]
  have hD : ∑ S ∈ E.powerset, (if (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) (insert s(x, y) S)) else 0)
      = w s(a, y) * w s(x, y) := by
    have : ∀ S ∈ E.powerset,
        (if (ofEdges (insert s(a, y) (insert s(x, y) S))).Reachable a y then
        weight (insert s(a, y) (insert s(x, y) E)) w (insert s(a, y) (insert s(x, y) S)) else 0)
        = w s(a, y) * w s(x, y) * weight E w S := by
      intro S hS
      rw [Finset.mem_powerset] at hS
      rw [if_pos (hCD S hS).2, weight_insert_mem he1 (hsubI S hS) w,
        weight_insert_mem he2 hS w]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, sum_weight, mul_one]
  rw [probOf, Finset.sum_powerset_insert he1, Finset.sum_powerset_insert he2,
    Finset.sum_powerset_insert he2, hA, hB, hC, hD]
  ring

/-! ### The gadget edge sets -/

/-- The spoke `a-v_j`. -/
private def spk (n j : ℕ) : Sym2 (Fin (n + 1)) := s((0 : Fin (n + 1)), ((j : ℕ) : Fin (n + 1)))

/-- The path edge `v_i-v_{i+1}`. -/
private def pth (n i : ℕ) : Sym2 (Fin (n + 1)) :=
  s(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1)))

/-- The edges of the gadget `G_n` supported on `{0, 1, ..., k}`. -/
private def Ek (n k : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  ((Finset.Ico 1 (k + 1)).image (spk n)) ∪ ((Finset.Ico 1 k).image (pth n))

private lemma Ico_one_succ (m : ℕ) (hm : 1 ≤ m) :
    Finset.Ico 1 (m + 1) = insert m (Finset.Ico 1 m) := by
  ext j
  simp only [Finset.mem_Ico, Finset.mem_insert]
  omega

private lemma cast_ne_cast {n a b : ℕ} (ha : a < n + 1) (hb : b < n + 1) (hab : a ≠ b) :
    ((a : ℕ) : Fin (n + 1)) ≠ ((b : ℕ) : Fin (n + 1)) := by
  intro h
  apply hab
  have := congrArg Fin.val h
  rwa [Fin.val_cast_of_lt ha, Fin.val_cast_of_lt hb] at this

private lemma cast_ne_zero' {n a : ℕ} (ha : a < n + 1) (ha0 : a ≠ 0) :
    ((a : ℕ) : Fin (n + 1)) ≠ 0 := by
  intro h
  apply ha0
  have := congrArg Fin.val h
  rwa [Fin.val_cast_of_lt ha, Fin.val_zero] at this

private lemma Ek_one (n : ℕ) : Ek n 1 = {spk n 1} := by
  simp [Ek]

private lemma Ek_succ (n k : ℕ) (hk : 1 ≤ k) :
    Ek n (k + 1) = insert (spk n (k + 1)) (insert (pth n k) (Ek n k)) := by
  have h1 : Finset.image (spk n) (Finset.Ico 1 (k + 1 + 1))
      = insert (spk n (k + 1)) (Finset.image (spk n) (Finset.Ico 1 (k + 1))) := by
    rw [Ico_one_succ (k + 1) (by omega), Finset.image_insert]
  have h2 : Finset.image (pth n) (Finset.Ico 1 (k + 1))
      = insert (pth n k) (Finset.image (pth n) (Finset.Ico 1 k)) := by
    rw [Ico_one_succ k hk, Finset.image_insert]
  simp only [Ek]
  rw [h1, h2, Finset.insert_union, Finset.union_insert]

/-- Every edge of `Ek n k` avoids the vertex `v_{k+1}`. -/
private lemma notMem_Ek (n k : ℕ) (hk : k + 1 ≤ n) :
    ∀ e ∈ Ek n k, ((k + 1 : ℕ) : Fin (n + 1)) ∉ e := by
  intro e he
  simp only [Ek, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at he
  rcases he with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨i, ⟨hi1, hi2⟩, rfl⟩
  · rw [spk, Sym2.mem_iff]
    refine not_or.2 ⟨?_, ?_⟩
    · exact cast_ne_zero' (by omega) (by omega)
    · exact cast_ne_cast (by omega) (by omega) (by omega)
  · rw [pth, Sym2.mem_iff]
    refine not_or.2 ⟨?_, ?_⟩
    · exact cast_ne_cast (by omega) (by omega) (by omega)
    · exact cast_ne_cast (by omega) (by omega) (by omega)

private lemma gadgetE_eq (n : ℕ) : gadgetE n = Ek n n := by
  ext e
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨u, v⟩, hcond, rfl⟩
    rcases hcond with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · subst hu
      refine Finset.mem_union_left _ ?_
      rw [Finset.mem_image]
      refine ⟨v.val, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        refine ⟨?_, v.isLt⟩
        rcases Nat.eq_zero_or_pos v.val with h | h
        · exact absurd (Fin.val_eq_zero_iff.1 h) hv
        · exact h
      · rw [spk, Fin.cast_val_eq_self]
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image]
      refine ⟨u.val, ?_, ?_⟩
      · rw [Finset.mem_Ico]
        have hvl : v.val < n + 1 := v.isLt
        have hu' : 1 ≤ u.val := hu
        have hv' : v.val = u.val + 1 := hv
        exact ⟨hu', by omega⟩
      · rw [pth, Fin.cast_val_eq_self]
        congr 1
        have hvl : v.val < n + 1 := v.isLt
        have hu' : 1 ≤ u.val := hu
        have hv' : v.val = u.val + 1 := hv
        have hh : (((u.val + 1 : ℕ)) : Fin (n + 1)).val = v.val := by
          rw [Fin.val_cast_of_lt (by omega)]; omega
        exact Fin.val_injective hh
  · intro he
    simp only [Ek, Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at he
    rcases he with ⟨j, ⟨hj1, hj2⟩, rfl⟩ | ⟨i, ⟨hi1, hi2⟩, rfl⟩
    · exact ⟨(0, ((j : ℕ) : Fin (n + 1))),
        Or.inl ⟨rfl, cast_ne_zero' (by omega) (by omega)⟩, rfl⟩
    · refine ⟨(((i : ℕ) : Fin (n + 1)), ((i + 1 : ℕ) : Fin (n + 1))), Or.inr ⟨?_, ?_⟩, rfl⟩
      · rw [Fin.val_cast_of_lt (by omega)]; omega
      · rw [Fin.val_cast_of_lt (by omega), Fin.val_cast_of_lt (by omega)]

/-! ### The recursion and its solution -/

private lemma probOf_Ek_one (n : ℕ) (P : ℚ) (hn : 1 ≤ n) :
    probOf (Ek n 1) (gadgetW n P)
        (fun S => (ofEdges S).Reachable 0 ((1 : ℕ) : Fin (n + 1))) = 1 - P := by
  have h1 : ((1 : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
  have hw : gadgetW n P (spk n 1) = 1 - P := by
    rw [gadgetW, spk]
    simp
  have hreach : (ofEdges ({spk n 1} : Finset (Sym2 (Fin (n + 1))))).Reachable 0
      ((1 : ℕ) : Fin (n + 1)) := by
    refine SimpleGraph.Adj.reachable ?_
    rw [adj_ofEdges]
    exact ⟨by simp [spk], Ne.symm h1⟩
  have hps : ({spk n 1} : Finset (Sym2 (Fin (n + 1)))).powerset = {∅, {spk n 1}} := by
    ext t
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  rw [probOf, Ek_one, hps, Finset.sum_insert (by simp),
    Finset.sum_singleton, if_neg (not_reach_isolated (Ne.symm h1) (by simp)), if_pos hreach]
  simp [weight, hw]

private lemma main (n : ℕ) (P : ℚ) (hn : 1 ≤ n) (hP : (1 : ℚ) + P ≠ 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n →
      probOf (Ek n k) (gadgetW n P)
          (fun S => (ofEdges S).Reachable 0 ((k : ℕ) : Fin (n + 1)))
        = (1 - P ^ (2 * k)) / (1 + P) := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
    intro _ hkn
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · simp only [Nat.zero_add, Nat.mul_one]
      rw [probOf_Ek_one n P hn]
      field_simp
      ring
    · have hkn' : k + 1 ≤ n := hkn
      have hy : ((k + 1 : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
      have hx : ((k : ℕ) : Fin (n + 1)) ≠ 0 := cast_ne_zero' (by omega) (by omega)
      have hxy : ((k : ℕ) : Fin (n + 1)) ≠ ((k + 1 : ℕ) : Fin (n + 1)) :=
        cast_ne_cast (by omega) (by omega) (by omega)
      have hax : (0 : Fin (n + 1)) ≠ ((k : ℕ) : Fin (n + 1)) := Ne.symm hx
      have hay : (0 : Fin (n + 1)) ≠ ((k + 1 : ℕ) : Fin (n + 1)) := Ne.symm hy
      have hspk : spk n (k + 1) = s((0 : Fin (n + 1)), ((k + 1 : ℕ) : Fin (n + 1))) := rfl
      have hpth : pth n k
          = s(((k : ℕ) : Fin (n + 1)), ((k + 1 : ℕ) : Fin (n + 1))) := rfl
      have hw1 : gadgetW n P s((0 : Fin (n + 1)), ((k + 1 : ℕ) : Fin (n + 1))) = 1 - P := by
        rw [gadgetW]
        simp
      have hw2 : gadgetW n P s(((k : ℕ) : Fin (n + 1)), ((k + 1 : ℕ) : Fin (n + 1))) = P := by
        have h0 : (0 : Fin (n + 1)) ∉
            s(((k : ℕ) : Fin (n + 1)), ((k + 1 : ℕ) : Fin (n + 1))) := by
          rw [Sym2.mem_iff]
          exact not_or.2 ⟨hax, hay⟩
        rw [gadgetW, if_neg h0]
      rw [Ek_succ n k hk1, hspk, hpth,
        probOf_pendant (Ek n k) (gadgetW n P) 0 ((k : ℕ) : Fin (n + 1))
          ((k + 1 : ℕ) : Fin (n + 1)) hax hay hxy (notMem_Ek n k hkn'),
        ih hk1 (by omega), hw1, hw2,
        show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
      field_simp
      ring

end L51

theorem solution (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    connProb (gadgetE n) (gadgetW n P) 0 (Fin.last n) = (1 - P ^ (2 * n)) / (1 + P) := by
  have hP : (1 : ℚ) + P ≠ 0 := by
    have : (0 : ℚ) < 1 + P := by linarith
    exact this.ne'
  have h := L51.main n P (by omega) hP n (by omega) le_rfl
  unfold connProb
  rw [L51.gadgetE_eq n, ← Fin.natCast_eq_last]
  exact h
