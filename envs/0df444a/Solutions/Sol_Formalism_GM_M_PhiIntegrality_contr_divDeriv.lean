-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_divDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:33.483135+00:00
-- url     : https://prove2.me/submissions/e0daccf4-ca80-44d0-bc49-503df1aa2f7a

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_linear
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_monomial
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_pderiv_pow_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (i : σ) (s : ℕ) :
    Contr 1 (((s.factorial : ℚ_[p]))⁻¹ •
      ((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)) := by

  intro B hB u hu
  refine bnd_linear _ zero_le_one (fun m => ?_) hu hB
  rw [LinearMap.smul_apply, pderiv_pow_monomial, MvPolynomial.smul_monomial, one_mul, smul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero s), one_mul]
  exact bnd_monomial _ _
end Formalism.GM.M.PhiIntegrality
