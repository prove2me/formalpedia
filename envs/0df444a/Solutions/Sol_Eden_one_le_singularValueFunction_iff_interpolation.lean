-- Prove2me | solution 1 for Eden.one_le_singularValueFunction_iff_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:15.516391+00:00
-- url     : https://prove2.me/submissions/046b8edf-3c97-41ff-8865-05afa9edd56f

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Theorems.Thm_Eden_singularValueFunction_evolution_pos
import Theorems.Thm_Eden_log_singularValueFunction_div_time


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ) :
    1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d ↔
      0 ≤ spectrumInterpolation (normalizedLogSingularValues c t p) d := by
  rw [← log_singularValueFunction_div_time c ht p d, le_div_iff₀ ht, zero_mul]
  exact (Real.log_nonneg_iff (singularValueFunction_evolution_pos c ht.le p d)).symm
end Eden
