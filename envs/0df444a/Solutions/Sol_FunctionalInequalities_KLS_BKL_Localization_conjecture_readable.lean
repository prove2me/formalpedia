-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.conjecture_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:52:08.131427+00:00
-- url     : https://prove2.me/submissions/40acc588-f808-43c6-bca3-444a36ebc9cc

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_ToCumulant
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantInduction
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Poincare
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cumulantBoundCompact_of_cutoffEnergyClaim_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_all_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffEnergyClaim_succ_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_generator_cumulantEnergy_ge_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_cumulantBound_of_compact_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_letwinCompactBound_readable
import Theorems.Thm_FunctionalInequalities_KLS_conjecture_of_cumulantBound_readable

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
/-- **BKL Theorem 4.1 for compactly supported laws, orders `d + 1 ≥ 3`**, conditional only on the compact Letwin bound (Lemma 4.2):
`∃ K ≥ 1, ∀ d ≥ 2, R^ν_{d+1} ≤ (d!)² K^d · Id` for all compactly supported isotropic log-concave `ν`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.exists_cumulantBoundCompact_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      LogConcave.Suspension.CumulantBoundCompact d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  refine ⟨153, by norm_num, fun d hd => ?_⟩
  have h := cumulantBoundCompact_of_cutoffEnergyClaim_readable (by norm_num : (0 : ℝ) ≤ 153)
    (cutoffEnergyClaim_of_letwinCompact hL d (by omega))
  rwa [envelope_succ_eq] at h
/-- **BKL Theorem 4.1, orders `d + 1 ≥ 3`** (all isotropic log-concave laws), conditional only on the compact Letwin bound:
the compact bound extends by the truncation argument of p. 19. The separate
`cumulantBound_of_letwinCompact` below also includes the base order `d + 1 = 2`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.exists_cumulantBound_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      LogConcave.Suspension.CumulantBound d ((d.factorial : ℝ) ^ 2 * K ^ d) := by
  obtain ⟨K, hK, hcompact⟩ := exists_cumulantBoundCompact_of_letwinCompact hL
  refine ⟨K, hK, ?_⟩
  intro d hd
  exact LogConcave.Suspension.cumulantBound_of_compact_readable
    (by omega : 1 ≤ d) (hcompact d hd)
end
end
end

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.BakryEmery
/-- **BKL Theorem 1.1 conditional on the compact Letwin bound**: the dimension-free KLS bound `KLS.Conjecture`
follows from Theorem 4.1 through the certified reduction `conjecture_of_cumulantBound`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.conjecture_of_letwinCompact (hL : LogConcave.Suspension.LetwinCompactBound) : KLS.Conjecture := by
  exact FunctionalInequalities.KLS.conjecture_of_cumulantBound_readable (hSource := exists_cumulantBound_of_letwinCompact hL)
universe u
/-- **The dimension-free KLS bound**, closed: `KLS.Conjecture` from the conditional assembly
`conjecture_of_letwinCompact` and the proved compact Letwin bound. -/
theorem solution : FunctionalInequalities.KLS.Conjecture :=
  FunctionalInequalities.KLS.BKL.Localization.conjecture_of_letwinCompact FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_readable
