-- Prove2me | solution 1 for FirstOrderOpt.Stochastic.stochastic_mirror_iterate_three_point_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:45:40.769794+00:00
-- url     : https://prove2.me/submissions/816811e7-1059-41ee-adcf-46fc6b5d40f9

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

open FirstOrderOpt.Prox in
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + ν.V xt xt1 ≤ γt * Gt x + ν.V xt x) :
    ∀ x ∈ X, γt * Gt (xt1 - x) + ν.V xt xt1 ≤ ν.V xt x - ν.V xt1 x := by
  intro x hx
  set f : E → ℝ := fun u => γt * Gt u + ν.V xt u with hf
  have hloc : IsLocalMinOn f X xt1 := by
    have : IsMinOn f X xt1 := fun u hu => hmin u hu
    exact this.localize
  have h1 : HasFDerivWithinAt (fun u => γt * Gt u) (γt • Gt) X xt1 :=
    (Gt.hasFDerivWithinAt).const_mul γt
  have h2 : HasFDerivWithinAt (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt))
      (ν.dω xt1 - ν.dω xt) X xt1 :=
    ((ν.hasFDerivWithinAt xt1 hxt1).sub_const _).sub
      ((ν.dω xt).hasFDerivWithinAt.sub_const _)
  have h3 : HasFDerivWithinAt f (γt • Gt + (ν.dω xt1 - ν.dω xt)) X xt1 := by
    have heq : f = (fun u => γt * Gt u) + (fun u => ν.ω u - ν.ω xt - (ν.dω xt u - ν.dω xt xt)) := by
      funext u
      simp only [hf, DistanceGeneratingFunction.V, map_sub, Pi.add_apply]
    rw [heq]
    exact h1.add h2
  have hy : x - xt1 ∈ posTangentConeAt X xt1 :=
    sub_mem_posTangentConeAt_of_segment_subset (hXconv.segment_subset hxt1 hx)
  have key := hloc.hasFDerivWithinAt_nonneg h3 hy
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, map_sub, smul_eq_mul] at key
  simp only [DistanceGeneratingFunction.V, map_sub]
  linarith
