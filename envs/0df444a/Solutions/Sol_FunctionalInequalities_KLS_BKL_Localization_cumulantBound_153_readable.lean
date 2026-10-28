-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.cumulantBound_153_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:52:34.385935+00:00
-- url     : https://prove2.me/submissions/5619afc2-47f6-4c36-960b-7559cc224d3b

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_ToCumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantInduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantBound
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBoundCompact_of_cutoffEnergyClaim_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_all_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_succ_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBound_of_compact_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_letwinCompactBound_readable

section
noncomputable section
section S7CClaimToBound
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
/-- The envelope at order `d + 1` is the constant of `conjecture_of_cumulantBound`: `b_{d+1} = (d!)² K^d`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.envelope_succ_eq (K : ℝ) (d : ℕ) : envelope K (d + 1) = (d.factorial : ℝ) ^ 2 * K ^ d := by
  unfold envelope
  rw [Nat.add_sub_cancel]
  exact mul_comm _ _
end
end S7CClaimToBound
end
end

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
/-- **BKL Theorem 4.1 with the explicit constant `153`, every order `d + 1 ≥ 2`** (the base `d = 1` included) and every
isotropic log-concave law, conditional only on the compact Letwin bound: the shared cutoff producer gives the compact
bound, and the truncation argument `cumulantBound_of_compact` removes compactness. -/
theorem FunctionalInequalities.KLS.BKL.Localization.cumulantBound_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∀ d : ℕ, 1 ≤ d →
      LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) := by
  intro d hd
  have h := cumulantBoundCompact_of_cutoffEnergyClaim_readable (by norm_num : (0 : ℝ) ≤ 153)
    (cutoffEnergyClaim_of_letwinCompact hL d hd)
  rw [envelope_succ_eq] at h
  exact LogConcave.Suspension.cumulantBound_of_compact_readable hd h
end
end
end

noncomputable section
/-- **BKL Theorem 4.1 with the explicit constant 153, closed**: every order `d + 1 ≥ 2` and every isotropic log-concave
law in every dimension. -/
theorem solution : ∀ d : ℕ, 1 ≤ d →
    FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * (153 : ℝ) ^ d) :=
  FunctionalInequalities.KLS.BKL.Localization.cumulantBound_of_letwinCompact FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_readable
