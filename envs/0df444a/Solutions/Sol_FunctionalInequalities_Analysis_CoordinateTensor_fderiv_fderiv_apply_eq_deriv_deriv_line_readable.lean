-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.fderiv_fderiv_apply_eq_deriv_deriv_line_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:26:58.235786+00:00
-- url     : https://prove2.me/submissions/301b03fd-ac48-4b90-92de-a266bd659577

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B1SecondOrderHelpers
variable {n r : ℕ}
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
