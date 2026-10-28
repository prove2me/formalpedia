-- Prove2me | solution 2 for AvramDividend.Classical.gaussian_vcstar_global_C2_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:37:16.517141+00:00
-- url     : https://prove2.me/submissions/008b3738-8bb9-4f8e-ab13-f24f1b20cc9c

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_of_positive_tilt
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
  obtain ⟨φ, hφ, -, hmono⟩ :=
    AvramDividend.Classical.gaussian_tilt_monotone_of_corrected_exit_identity X q hq W hW hσ hExit
  exact AvramDividend.Classical.vcstar_global_C2_gaussian_of_positive_tilt X hX q hq W hW
    (ENNReal.toReal_pos hcpos.ne' hc.ne) hσ ⟨φ, hφ, hmono⟩
