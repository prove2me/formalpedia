-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaTaylorLow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:29:02.676144+00:00
-- url     : https://prove2.me/submissions/094a07b8-9cda-42b4-82bb-6d3c6519b27a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_sigma_sub_id_bound
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_iteratedDeriv_eq_zero_of_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Filter
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open ModifiedSigmaBounds
open ModifiedSigmaBounds
namespace Formalism.L2.Th1.F
theorem _root_.solution (he : SigmaEntire) (hs : SigmaSummable) :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 := by
  intro L
  obtain ⟨K, r, hr, hb⟩ := sigma_sub_id_bound hs L
  have hd : Differentiable ℂ (fun z => wSigma L z - z) := (he L).sub differentiable_id
  have key : ∀ n : ℕ, n < 4 → n ≠ 1 → iteratedDeriv n (wSigma L) 0 = 0 := by
    intro n hn hn1
    have h0 := iteratedDeriv_eq_zero_of_bound hd hr hb n hn
    rw [iteratedDeriv_fun_sub ((he L).contDiff.contDiffAt) (contDiff_fun_id.contDiffAt),
      iteratedDeriv_fun_id_zero, if_neg hn1, sub_zero] at h0
    exact h0
  exact ⟨key 2 (by norm_num) (by norm_num), key 3 (by norm_num) (by norm_num)⟩
end Formalism.L2.Th1.F
