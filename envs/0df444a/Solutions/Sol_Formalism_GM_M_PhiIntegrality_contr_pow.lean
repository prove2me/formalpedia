-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:12.483338+00:00
-- url     : https://prove2.me/submissions/53ee7fa0-2135-4819-80c4-80c89123b6f4

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_comp

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
theorem _root_.solution {C : ℝ} (hC : 0 ≤ C) {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (h : Contr C T) (j : ℕ) : Contr (C ^ j) (T ^ j) := by

  induction j with
  | zero =>
    intro B hB u hu
    simpa using hu
  | succ j ih =>
    rw [pow_succ' C j, pow_succ T j]
    exact contr_comp hC h ih
end Formalism.GM.M.PhiIntegrality
