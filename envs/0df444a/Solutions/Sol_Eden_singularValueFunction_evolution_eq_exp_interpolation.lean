-- Prove2me | solution 1 for Eden.singularValueFunction_evolution_eq_exp_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:02:38.669153+00:00
-- url     : https://prove2.me/submissions/138715a2-86e5-40a2-850c-9ab1ce5721c7

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_PeriodicGlobalGrowth
import Theorems.Thm_Eden_log_singularValueFunction_div_time
import Theorems.Thm_Eden_singularValueFunction_evolution_pos


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ}
    (ht : 0 < t) (p : PhaseSpace) (d : ℝ) :
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (t * spectrumInterpolation (normalizedLogSingularValues c t p) d) := by
  calc
    _ = Real.exp (Real.log (singularValueFunction
        (fderiv ℝ (evolution c t) p).toLinearMap d)) :=
      (Real.exp_log (singularValueFunction_evolution_pos c ht.le p d)).symm
    _ = _ := by
      congr 1
      have h := (div_eq_iff ht.ne').mp (log_singularValueFunction_div_time c ht p d)
      linarith
end Eden
