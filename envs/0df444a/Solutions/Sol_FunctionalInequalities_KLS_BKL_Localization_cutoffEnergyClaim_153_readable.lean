-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_153_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:51:48.094128+00:00
-- url     : https://prove2.me/submissions/ff1b53aa-0faa-4487-baeb-e3b1d0f74150

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantInduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantBound
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBoundCompact_of_cutoffEnergyClaim_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_all_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_succ_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_letwinCompactBound_readable

section
noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
section
/-- **Lemma 5.1 discharges its named hypothesis**: `Lemma51Bound` holds, by `generator_cumulantEnergy_ge`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.lemma51Bound : Lemma51Bound := by
  unfold Lemma51Bound
  intro n μ hc hiso hLC h8 r hr u q hSym hQ
  exact generator_cumulantEnergy_ge_readable μ hc hiso hLC h8 hr u q hSym hQ
/-- **BKL (95) in finite-horizon cutoff form, every order `d + 1 ≥ 2`**, at `K = 153`, conditional only on the compact
Letwin bound. This is the single assembly of the induction: the step `cutoffEnergyClaim_succ` with `lemma51Bound` and the
claim-to-bound passage `cumulantBoundCompact_of_cutoffEnergyClaim`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∀ d : ℕ, 1 ≤ d → CutoffEnergyClaim 153 d :=
  cutoffEnergyClaim_all_readable hL (le_refl 153)
    (fun _ hm ih ihb => cutoffEnergyClaim_succ_readable hL lemma51Bound (le_refl 153) hm ih ihb)
    (fun _ h => cumulantBoundCompact_of_cutoffEnergyClaim_readable (by norm_num : (0 : ℝ) ≤ 153) h)
end
end
end

noncomputable section
/-- **BKL (95), finite-horizon cutoff form, closed**: every order `d + 1 ≥ 2` at `K = 153`, from the proved compact
Letwin bound. -/
theorem solution : ∀ d : ℕ, 1 ≤ d → FunctionalInequalities.KLS.BKL.Localization.CutoffEnergyClaim 153 d :=
  FunctionalInequalities.KLS.BKL.Localization.cutoffEnergyClaim_of_letwinCompact FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_readable
