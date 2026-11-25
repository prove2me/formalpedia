-- Prove2me | solution 1 for Formalism.L2.Th1.F.sgStarNormPeriodic_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:22:20.210432+00:00
-- url     : https://prove2.me/submissions/f4f4c844-dcc4-4630-a555-8fbeee909c49

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaConv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SgStar
import Theorems.Thm_Formalism_L2_Th1_F_ModifiedSigmaBounds_norm_semiChar

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
namespace Formalism.L2.Th1.F
theorem _root_.solution (h : SgStarQuasi) : SgStarNormPeriodic := by
  intro L ω z hω
  rw [h L ω z hω, norm_mul, norm_mul, norm_semiChar, one_mul, mul_pow, Complex.norm_exp,
    ← Real.exp_nat_mul, mul_right_comm, ← Real.exp_add, mul_comm]
  congr 2
  have h1 : ‖z + ω‖ ^ 2 = ‖z‖ ^ 2 + ‖ω‖ ^ 2 + 2 * (z * conj ω).re := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  have h2 : (ω * conj ω).re = ‖ω‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
  have h3 : ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2).re
      = Real.pi * ((z * conj ω).re / area L) + Real.pi * (‖ω‖ ^ 2 / area L) / 2 := by
    rw [← h2, herm, herm, ← Complex.div_ofReal_re, ← Complex.div_ofReal_re]
    simp
  rw [h3, h1]
  push_cast
  ring
end Formalism.L2.Th1.F
