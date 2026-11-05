-- Prove2me | solution 1 for FiniteEnergyPlane.integral_liouvilleForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T22:59:36.476978+00:00
-- url     : https://prove2.me/submissions/b52dd113-9d6d-4421-a481-b269b7f61c96

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_liouville_ofR4_ofR4
import Mathlib.Analysis.Calculus.Deriv.Prod



namespace FiniteEnergyPlane

theorem integral_liouvilleForm_eq_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (R : HryniewiczCriterion.PeriodicOrbit H₀) :
    (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) =
      ∫ τ in (0 : ℝ)..R.T, liouville (ofR4 (R.x τ)) (deriv (fun s => ofR4 (R.x s)) τ) := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hd := R.trajectory.1 t
  have hd' : HasDerivAt (fun s => ofR4 (R.x s)) (ofR4 (deriv R.x t)) t := by
    rw [hd.deriv]
    exact hasDerivAt_pi.2 fun k => (hasDerivAt_pi.1 hd) (Fin.cast (by norm_num) k)
  change HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t) =
    liouville (ofR4 (R.x t)) (deriv (fun s => ofR4 (R.x s)) t)
  rw [hd'.deriv, liouville_ofR4_ofR4]

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (R : HryniewiczCriterion.PeriodicOrbit H₀) :
    (∫ t in (0 : ℝ)..R.T, HryniewiczCriterion.liouvilleForm (R.x t) (deriv R.x t)) =
      ∫ τ in (0 : ℝ)..R.T, liouville (ofR4 (R.x τ)) (deriv (fun s => ofR4 (R.x s)) τ) :=
  integral_liouvilleForm_eq_aux H₀ R
