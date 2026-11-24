-- Prove2me | solution 1 for Formalism.L2.Th1.F.CmBy.normSq_omega
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:27.389205+00:00
-- url     : https://prove2.me/submissions/d5ec27e4-fee1-4235-b5db-b87049a38911

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_QuasiPeriodConstIsogeny
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HasCMByIsogenyOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
namespace Formalism.L2.Th1.F
namespace CmBy
private lemma re_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).re = (m : ℝ) + (n : ℝ) / 2 := by
  simp [omegaK]
  ring
private lemma im_add_mul_omegaK (d : ℕ) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK d).im = (n : ℝ) * Real.sqrt d / 2 := by
  simp [omegaK]
  ring
end CmBy
end Formalism.L2.Th1.F
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (omegaK HasCMBy)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.CmBy
namespace Formalism.L2.Th1.F.CmBy
theorem _root_.solution (d : ℕ) (m n : ℤ) :
    Complex.normSq ((m : ℂ) + (n : ℂ) * omegaK d)
      = (m : ℝ) ^ 2 + (m : ℝ) * (n : ℝ) + (n : ℝ) ^ 2 * ((1 + (d : ℝ)) / 4) := by
  have hs : Real.sqrt (d : ℝ) * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  rw [Complex.normSq_apply, re_add_mul_omegaK, im_add_mul_omegaK]
  linear_combination ((n : ℝ) ^ 2 / 4) * hs
end Formalism.L2.Th1.F.CmBy
