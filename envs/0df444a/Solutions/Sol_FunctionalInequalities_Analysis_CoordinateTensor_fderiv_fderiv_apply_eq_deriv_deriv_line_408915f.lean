-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_apply_eq_deriv_deriv_line_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:53:23.505494+00:00
-- url     : https://prove2.me/submissions/5acb1c57-a78d-40d7-a785-37dafa821312

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B1SecondOrderHelpers
open Matrix
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities.Analysis.CoordinateTensor in
set_option maxHeartbeats 800000 in
/-- The second directional derivative is the second derivative along the line. -/
theorem solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : W → ℝ} {y : W} (hΦ : ContDiffAt ℝ 2 Φ y) (v : W) :
    fderiv ℝ (fderiv ℝ Φ) y v v = deriv (deriv fun ε : ℝ => Φ (y + ε • v)) 0 := by
  have hc : ContDiffAt ℝ 1 (fderiv ℝ Φ) y :=
    hΦ.fderiv_right (by norm_num)
  have hl (t : ℝ) : HasDerivAt (fun a : ℝ => y + a • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add y
  have hp :
      HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y)
        (y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hd :
      HasDerivAt (fun t : ℝ => fderiv ℝ Φ (y + t • v))
        (fderiv ℝ (fderiv ℝ Φ) y v) 0 :=
    hp.comp_hasDerivAt 0 (hl 0)
  have hd' :
      deriv (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) 0 =
        fderiv ℝ (fderiv ℝ Φ) y v v := by
    simpa only [map_zero, add_zero] using
      (hd.clm_apply (hasDerivAt_const (0 : ℝ) v)).deriv
  have ht :
      Filter.Tendsto (fun t : ℝ => y + t • v) (nhds 0) (nhds y) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using (hl 0).continuousAt
  have heq :
      (deriv fun t : ℝ => Φ (y + t • v)) =ᶠ[nhds 0]
        (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) := by
    filter_upwards [ht.eventually (hΦ.eventually (by norm_num))] with t h
    exact
      ((h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  exact hd'.symm.trans heq.deriv_eq.symm
