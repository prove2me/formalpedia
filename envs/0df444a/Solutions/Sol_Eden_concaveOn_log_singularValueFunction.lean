-- Prove2me | solution 1 for Eden.concaveOn_log_singularValueFunction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:24.564865+00:00
-- url     : https://prove2.me/submissions/254b8dfd-3e1a-4df7-b890-f8347f083965

import Definitions.Def_Eden_LogarithmicInterpolation
import Mathlib.Analysis.Convex.Function
import Definitions.Def_Eden_InterpolationConcavity
import Theorems.Thm_Eden_concaveOn_spectrumInterpolation
import Theorems.Thm_Eden_log_singularValueFunction_div_time
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    ConcaveOn ℝ (Icc (0 : ℝ) 5) (fun d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t) := by
  apply (concaveOn_spectrumInterpolation
    (normalizedLogSingularValues_antitone c ht p)).congr
  intro d hd
  exact (log_singularValueFunction_div_time c ht p d).symm
end Eden
