-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.bnd_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:39.217873+00:00
-- url     : https://prove2.me/submissions/b444566b-475f-4dfa-ab5d-2d96bb4fff73

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_sum
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_smul
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_mono

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
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) {C B : ℝ} (hC : 0 ≤ C)
    (hT : ∀ m, Bnd C (T (monomial m 1))) {u : MvPolynomial σ ℚ_[p]} (hu : Bnd B u) (hB : 0 ≤ B) :
    Bnd (B * C) (T u) := by

  have e : T u = ∑ v ∈ u.support, u.coeff v • T (monomial v 1) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine bnd_sum _ _ (mul_nonneg hB hC) fun v _ => ?_
  exact bnd_mono (bnd_smul (u.coeff v) (hT v)) (mul_le_mul_of_nonneg_right (hu v) hC)
end Formalism.GM.M.PhiIntegrality
