-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsD.zero_l_class_correspondence
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:26:41.610976+00:00
-- url     : https://prove2.me/submissions/51addd09-9ff8-4026-bcc6-f9870a420b68

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ConvexClosureVal
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLR
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZ
import Definitions.Def_DiscreteConvex_LConvexFunctionsD_ZeroLZR

open Classical
open scoped Pointwise

namespace DisZLC
open DiscreteConvex.LConvexFunctionsD

noncomputable def g : (Fin 2 → ℝ) → WithTop ℝ := fun p => if p 1 < p 0 then 0 else ⊤

lemma zeroLR : ZeroLR g := by
  refine ⟨?_, ⟨0, ?_⟩, ?_⟩
  · intro p q
    simp only [g]
    by_cases hp : p 1 < p 0
    · by_cases hq : q 1 < q 0
      · have h1 : (p ⊔ q) 1 < (p ⊔ q) 0 := by
          simp only [Pi.sup_apply]
          exact max_lt (lt_max_of_lt_left hp) (lt_max_of_lt_right hq)
        have h2 : (p ⊓ q) 1 < (p ⊓ q) 0 := by
          simp only [Pi.inf_apply]
          exact lt_min ((min_le_left _ _).trans_lt hp) ((min_le_right _ _).trans_lt hq)
        rw [if_pos hp, if_pos hq, if_pos h1, if_pos h2]
      · rw [if_neg hq]; simp
    · rw [if_neg hp]; simp
  · intro p α
    simp [g]
  · intro x t ht
    simp only [g]
    by_cases h : x 1 < x 0
    · have h' : t * x 1 < t * x 0 := mul_lt_mul_of_pos_left h ht
      rw [if_pos h, if_pos h']
      simp [PosScalarMul]
    · have h' : ¬ t * x 1 < t * x 0 := fun h' => h (lt_of_mul_lt_mul_left h' ht.le)
      rw [if_neg h, if_neg h']
      simp [PosScalarMul, ht.ne']

lemma argmin_eq : ArgMinR (LinearWeightR g 0) = {x | x 1 < x 0} := by
  ext x
  simp only [ArgMinR, LinearWeightR, Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero,
    WithTop.coe_zero, add_zero, Set.mem_ofPred_eq]
  constructor
  · intro hx
    have := hx ![1, 0]
    by_contra hc
    simp [g, hc] at this
  · intro hx q
    simp only [g, if_pos hx]
    split_ifs <;> simp

lemma not_integral : ¬ IntegralPolyhedralFunctionR g := by
  intro h
  have hne : (ArgMinR (LinearWeightR g 0)).Nonempty := ⟨![1, 0], by rw [argmin_eq]; simp⟩
  have hI := h 0 hne
  rw [argmin_eq] at hI
  have hmem : (![1/2, 0] : Fin 2 → ℝ) ∈ {x : Fin 2 → ℝ | x 1 < x 0} := by
    simp only [Set.mem_ofPred_eq]; norm_num
  rw [hI] at hmem
  have hsub : convexHull ℝ ({x : Fin 2 → ℝ | x 1 < x 0} ∩ {x | ∀ v, ∃ k : ℤ, x v = (k : ℝ)})
      ⊆ {x : Fin 2 → ℝ | 1 ≤ x 0 - x 1} := by
    refine convexHull_min ?_ ?_
    · rintro x ⟨hx, hk⟩
      obtain ⟨k0, hk0⟩ := hk 0
      obtain ⟨k1, hk1⟩ := hk 1
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [hk0, hk1] at hx ⊢
      have : k1 < k0 := by exact_mod_cast hx
      have : k1 + 1 ≤ k0 := this
      have : ((k1 : ℝ) + 1) ≤ (k0 : ℝ) := by exact_mod_cast this
      linarith
    · refine convex_halfSpace_ge ?_ 1
      exact ⟨fun x y => by simp; ring, fun c x => by simp; ring⟩
  have := hsub hmem
  simp only [Set.mem_ofPred_eq] at this
  norm_num at this

end DisZLC

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V],
    (∀ g : (V → ℝ) → WithTop ℝ, DiscreteConvex.LConvexFunctionsD.ZeroLZR g ↔
      DiscreteConvex.LConvexFunctionsD.ZeroLR g) ∧
    (∀ g : (V → ℤ) → WithTop ℝ, DiscreteConvex.LConvexFunctionsD.ZeroLZ g →
      DiscreteConvex.LConvexFunctionsD.ZeroLR
        (fun p => DiscreteConvex.LConvexFunctionsD.ConvexClosureVal g p))) := by
  intro h
  have := ((h (V := Fin 2)).1 DisZLC.g).2 DisZLC.zeroLR
  exact DisZLC.not_integral this.2
