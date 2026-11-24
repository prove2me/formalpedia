-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.contr_D
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:42.695671+00:00
-- url     : https://prove2.me/submissions/4a7a9325-28d2-400f-a24e-d1ed24a1accf

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_commute_pderiv
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_contr_divDeriv
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
theorem _root_.solution (i j : σ) (k : ℕ) :
    Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv j).toLinearMap) ^ k)) := by

  have e : (((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv j).toLinearMap) ^ k) =
      ((((k.factorial : ℚ_[p]))⁻¹ •
        ((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ k)) *
      (((k.factorial : ℚ_[p]))⁻¹ •
        ((pderiv j : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ k))) := by
    rw [smul_mul_smul_comm, ← mul_inv, ← sq, ← (commute_pderiv i j).mul_pow, Module.End.mul_eq_comp]
  rw [e]
  simpa using contr_comp zero_le_one (contr_divDeriv j k) (contr_divDeriv i k)
end Formalism.GM.M.PhiIntegrality
