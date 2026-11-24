-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.norm_choose_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:09.139751+00:00
-- url     : https://prove2.me/submissions/5e149e9f-a09d-4e33-a8e0-b2db5376a607

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_Formalism_GM_M_PhiIntegrality_norm_natCast_inv_le

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
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (j k : ℕ) (hk : k ≤ j) :
    ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (Nat.log p j) := by

  calc _ ≤ (p : ℝ) ^ ((j.choose k).factorization p) := norm_natCast_inv_le _ (Nat.choose_pos hk).ne'
    _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
        Nat.factorization_choose_le_log
end Formalism.GM.M.PhiIntegrality
