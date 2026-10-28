-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.exists_isotropicBound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:58:22.968765+00:00
-- url     : https://prove2.me/submissions/071595e5-32c6-45bb-a737-4d0a6503a120

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Poincare
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBound_153_readable
import Theorems.Thm_FunctionalInequalities_KLS_localSlope_le_of_cumulantBound_all_readable

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
universe u
/-- **BKL Theorem 1.1** (arXiv:2610.05474v1, p. 2), closed: one universal constant `C > 0` bounds the literature
Poincaré constant of every isotropic log-concave probability measure on every finite-dimensional real inner product
space (universe `u`), with `K = 153` from the closed `cumulantBound_153`. -/
theorem solution : ∃ C : NNReal, 0 < C ∧ FunctionalInequalities.KLS.IsotropicBound.{u} C := by
  obtain ⟨C, hC, hAll⟩ := FunctionalInequalities.KLS.localSlope_le_of_cumulantBound_all_readable.{u}
  have hcb : ∀ d : ℕ, 2 ≤ d →
      FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) :=
    fun d hd => FunctionalInequalities.KLS.BKL.Localization.cumulantBound_153_readable d (by omega)
  let B : NNReal := ⟨2 * C * 153, by positivity⟩
  have hB : (B : ENNReal) = ENNReal.ofReal (2 * C * 153) := ENNReal.ofReal_coe_nnreal.symm
  refine ⟨B, ?_, ?_⟩
  · change (0 : ℝ) < 2 * C * 153
    positivity
  · intro E _ _ _ _ _ _ _ μ hLC hiso
    rw [hB]
    exact hAll 153 (by norm_num) hcb E μ hLC hiso
