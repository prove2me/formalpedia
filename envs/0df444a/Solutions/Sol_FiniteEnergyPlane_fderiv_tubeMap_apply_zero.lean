-- Prove2me | solution 1 for FiniteEnergyPlane.fderiv_tubeMap_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-16T10:59:50.333364+00:00
-- url     : https://prove2.me/submissions/4e1d4a51-97ff-4187-b8ac-3b04b24d0a17

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic



/-!
# The derivative of `(z, w) ↦ u z + N z w` along `w = 0` (standalone helper).
-/

namespace FiniteEnergyPlane

namespace SMEF

theorem fderiv_tubeMap_apply_zero_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (N : ℂ → ℂ →L[ℝ] F) (hu : Differentiable ℝ u) (hN : Differentiable ℝ N)
    (z Δ ν : ℂ) :
    fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν := by
  have h1 : HasFDerivAt (fun q : ℂ × ℂ => u q.1)
      ((fderiv ℝ u z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hu z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have hc : HasFDerivAt (fun q : ℂ × ℂ => N q.1)
      ((fderiv ℝ N z).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)) (z, 0) :=
    (hN z).hasFDerivAt.comp (z, (0 : ℂ)) hasFDerivAt_fst
  have h2 := hc.clm_apply (hasFDerivAt_snd (p := ((z, 0) : ℂ × ℂ)))
  have h3 : HasFDerivAt (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) _ (z, 0) := h1.add h2
  rw [h3.fderiv]
  simp

end SMEF

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : ℂ → F) (N : ℂ → ℂ →L[ℝ] F) (hu : Differentiable ℝ u) (hN : Differentiable ℝ N)
    (z Δ ν : ℂ) :
    fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) = fderiv ℝ u z Δ + N z ν :=
  SMEF.fderiv_tubeMap_apply_zero_aux u N hu hN z Δ ν
