-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:12.20183+00:00
-- url     : https://prove2.me/submissions/d116d72c-dd9e-41c4-97bc-c1ab410a1b70

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_sum
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_linear
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_monomial

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
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) : Contr (p := p) 1 (Formalism.GM.tieE (k := ℚ_[p]) w e) := by

  intro B hB u hu
  refine bnd_linear _ zero_le_one (fun m => ?_) hu hB
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, Finset.sum_mul]
  refine bnd_sum _ _ zero_le_one fun c _ => ?_
  rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_mul,
    show (1 : ℚ_[p]) * 1 * 1 = ((1 : ℕ) : ℚ_[p]) by simp]
  exact bnd_monomial _ _
end Formalism.GM.M.PhiIntegrality
