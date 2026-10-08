-- Prove2me | solution 1 for FirstOrderOpt.Deterministic.mirror_iterate_three_point_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:46:11.223179+00:00
-- url     : https://prove2.me/submissions/69ea7e6a-3618-4fc1-b0cb-bb3dfff633eb

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (xt xt1 : E) (gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * gt xt1 + ν.V xt xt1 ≤ γt * gt x + ν.V xt x) :
    ∀ x ∈ X, γt * gt (xt1 - x) + ν.V xt xt1 ≤ ν.V xt x - ν.V xt1 x := by
  intro x hx
  set f : E → ℝ := fun u => γt * gt u + (ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt)) with hf
  have hfV : ∀ u, f u = γt * gt u + ν.V xt u := by
    intro u
    simp only [hf, DistanceGeneratingFunction.V, map_sub]
  have hloc : IsLocalMinOn f X xt1 := by
    refine Filter.eventually_of_mem self_mem_nhdsWithin (fun u hu => ?_)
    show f xt1 ≤ f u
    rw [hfV, hfV]
    exact hmin u hu
  have hder : HasFDerivWithinAt f
      (γt • gt + (ν.dω xt1 - ν.dω xt)) X xt1 := by
    have h1 : HasFDerivWithinAt (fun u => γt * gt u) (γt • gt) X xt1 :=
      gt.hasFDerivWithinAt.const_mul γt
    have h2 : HasFDerivWithinAt (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt))
        (ν.dω xt1 - ν.dω xt) X xt1 :=
      ((ν.hasFDerivWithinAt xt1 hxt1).sub_const _).sub
        ((ν.dω xt).hasFDerivWithinAt.sub_const _)
    exact h1.add h2
  have hseg : segment ℝ xt1 x ⊆ X := hXconv.segment_subset hxt1 hx
  have hcone := sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnn := hloc.hasFDerivWithinAt_nonneg hder hcone
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, map_sub] at hnn
  simp only [DistanceGeneratingFunction.V, map_sub]
  linarith
