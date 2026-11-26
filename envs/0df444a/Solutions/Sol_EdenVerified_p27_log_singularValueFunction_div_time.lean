-- Prove2me | solution 1 for EdenVerified.p27_log_singularValueFunction_div_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:36.944082+00:00
-- url     : https://prove2.me/submissions/ba22e18b-5b9f-4810-a32c-36858142a094

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_log_singularValueFunction_div_time


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ),
    Real.log (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t =
      spectrumInterpolation (normalizedLogSingularValues c t p) d :=
  @Eden.log_singularValueFunction_div_time
end EdenVerified
