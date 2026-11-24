-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wtSpC_iff_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:59.926157+00:00
-- url     : https://prove2.me/submissions/19091b2c-924b-4ac9-8c6d-404d98750c97

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_coeff_glAct_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p LL j Cs la ↔ ∀ c ∈ Cs, glAct p LL j c c x = ((la c : ℤ) : ℚ_[p]) • x := by
  rw [WtSpC, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h c hc
    ext m
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul]
    by_cases hm : coeff m x = 0
    · rw [hm, mul_zero, mul_zero]
    · have := h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c hc
      rw [this]
  · intro h m hm c hc
    have hm' : coeff m x ≠ 0 := mem_support_iff.mp (Finset.mem_coe.mp hm)
    have e := congrArg (coeff m) (h c hc)
    rw [coeff_glAct_diag, coeff_smul, smul_eq_mul] at e
    have := mul_right_cancel₀ hm' e
    exact_mod_cast this
end Formalism.InvariantFactorPaths.PW
