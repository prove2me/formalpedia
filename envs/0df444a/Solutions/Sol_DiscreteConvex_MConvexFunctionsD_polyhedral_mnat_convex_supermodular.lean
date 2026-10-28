-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.polyhedral_mnat_convex_supermodular
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:29:20.673868+00:00
-- url     : https://prove2.me/submissions/e20d9d65-61cf-4a6d-81b1-df86a8fa951d

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR

open scoped Pointwise
open Classical

namespace DisPMS
open DiscreteConvex.MConvexFunctionsD

/-- Indicator (value 0) of `{x | ∑ x = 0, x i ≠ 0 for some i ∈ I}`. -/
noncomputable def F {W : Type} [Fintype W] (I : Set W) : (W → ℝ) → WithTop ℝ :=
  fun x => if ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 then 0 else ⊤

lemma charvec_sum {W : Type} [Fintype W] [DecidableEq W] (u : W) :
    ∑ w, ((CharVec u w : ℤ) : ℝ) = 1 := by
  simp [CharVec]

lemma charvec_abs {W : Type} [DecidableEq W] (u v w : W) :
    |((CharVec u w : ℤ) : ℝ) - ((CharVec v w : ℤ) : ℝ)| ≤ 1 := by
  unfold CharVec; split_ifs <;> norm_num

lemma exch {W : Type} [Fintype W] [DecidableEq W] (I : Set W) : MExchangeAxiomR (F I) := by
  intro x hx y hy u hu
  have hx' : ∑ w, x w = 0 ∧ ∃ i ∈ I, x i ≠ 0 := by
    by_contra hc; exact hx (if_neg hc)
  have hy' : ∑ w, y w = 0 ∧ ∃ i ∈ I, y i ≠ 0 := by
    by_contra hc; exact hy (if_neg hc)
  have hfx : F I x = 0 := if_pos hx'
  have hfy : F I y = 0 := if_pos hy'
  obtain ⟨hxs, i, hiI, hxi⟩ := hx'
  obtain ⟨hys, j, hjI, hyj⟩ := hy'
  obtain ⟨v, hv⟩ : ∃ v, x v < y v := by
    by_contra hc
    push Not at hc
    have : ∑ w, y w < ∑ w, x w :=
      Finset.sum_lt_sum (fun w _ => hc w) ⟨u, Finset.mem_univ _, hu⟩
    linarith
  have hm : 0 < min |x i| |y j| := lt_min (abs_pos.2 hxi) (abs_pos.2 hyj)
  refine ⟨v, hv, min |x i| |y j| / 2, half_pos hm, fun α h0 h1 => ?_⟩
  have hlx : α < |x i| := by have := min_le_left |x i| |y j|; linarith
  have hly : α < |y j| := by have := min_le_right |x i| |y j|; linarith
  have key1 : F I (fun w => x w - α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, i, hiI, ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hxs]; ring
    · intro h
      have hb := charvec_abs u v i
      have e : x i = α * (((CharVec u i : ℤ) : ℝ) - ((CharVec v i : ℤ) : ℝ)) := by linarith
      have : |x i| ≤ α := by
        rw [e, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  have key2 : F I (fun w => y w + α * (CharVec u w - CharVec v w : ℝ)) = 0 := by
    apply if_pos
    refine ⟨?_, j, hjI, ?_⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, charvec_sum,
        charvec_sum, hys]; ring
    · intro h
      have hb := charvec_abs u v j
      have e : y j = -(α * (((CharVec u j : ℤ) : ℝ) - ((CharVec v j : ℤ) : ℝ))) := by linarith
      have : |y j| ≤ α := by
        rw [e, abs_neg, abs_mul, abs_of_nonneg h0]
        nlinarith
      linarith
  rw [key1, key2, hfx, hfy]

noncomputable def f : (Fin 2 → ℝ) → WithTop ℝ := fun p => if ∃ i, p i ≠ 0 then 0 else ⊤

lemma lift_eq : LiftedFunctionR f = F (Set.range (some : Fin 2 → Option (Fin 2))) := by
  funext X
  simp only [LiftedFunctionR, F, f, Fintype.sum_option]
  have e1 : (X none = -∑ v, X (some v)) ↔ X none + ∑ v, X (some v) = 0 := by
    constructor <;> intro h <;> linarith
  have e2 : (∃ i, X (some i) ≠ 0) ↔ ∃ i ∈ Set.range (some : Fin 2 → Option (Fin 2)), X i ≠ 0 :=
    ⟨fun ⟨i, hi⟩ => ⟨some i, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ => ⟨i, hi⟩⟩
  by_cases h1 : X none = -∑ v, X (some v)
  · by_cases h2 : ∃ i, X (some i) ≠ 0
    · rw [if_pos h1, if_pos h2, if_pos ⟨e1.1 h1, e2.1 h2⟩]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (e2.2 h.2))]
  · rw [if_neg h1, if_neg (fun h => h1 (e1.2 h.1))]

lemma hf : MNaturalConvexR f := by
  unfold MNaturalConvexR
  rw [lift_eq]
  exact exch _

lemma not_super : ¬ ∀ x y : Fin 2 → ℝ,
    f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v)) := by
  intro h
  have := h 0 ![1, -1]
  simp [f, Fin.exists_fin_two] at this

end DisPMS

open DiscreteConvex.MConvexFunctionsD in
theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ) (_hf : MNaturalConvexR f),
    ∀ x y : V → ℝ, f x + f y ≤ f (fun v => max (x v) (y v)) + f (fun v => min (x v) (y v))) := by
  intro h
  exact DisPMS.not_super (h (V := Fin 2) DisPMS.f DisPMS.hf)
