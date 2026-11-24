-- Prove2me | solution 1 for Formalism.L2.Th1.F.sigmaZero_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:37:45.805997+00:00
-- url     : https://prove2.me/submissions/68132087-156a-4fa4-ad05-ad31be1dc16e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaBasic
import Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_wFactor_eq_zero_iff
import Theorems.Thm_Formalism_L2_Th1_F_SigmaBasic_wFactor_zero_left

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
open SigmaBasic
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SigmaSummable) : SigmaZero := by
  intro L z
  unfold wSigma
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with hz | hp
    · rw [hz]
      exact zero_mem _
    · by_contra hz
      have hne : ∀ l : L.lattice, wFactor (l : ℂ) z ≠ 0 := by
        intro l hl
        by_cases hl0 : (l : ℂ) = 0
        · rw [hl0, wFactor_zero_left] at hl
          exact one_ne_zero hl
        · rw [wFactor_eq_zero_iff hl0] at hl
          exact hz (by rw [hl]; exact l.2)
      have hs : Summable (fun l : L.lattice => Complex.log (wFactor (l : ℂ) z)) := by
        have := Complex.summable_log_one_add_of_summable (Summable.of_norm (h L z))
        simpa only [add_sub_cancel] using this
      rw [← Complex.cexp_tsum_eq_tprod hne hs] at hp
      exact Complex.exp_ne_zero _ hp
  · intro hz
    by_cases hz0 : z = 0
    · rw [hz0, zero_mul]
    · rw [tprod_of_exists_eq_zero ⟨⟨z, hz⟩, (wFactor_eq_zero_iff hz0 z).mpr rfl⟩, mul_zero]
end Formalism.L2.Th1.F
