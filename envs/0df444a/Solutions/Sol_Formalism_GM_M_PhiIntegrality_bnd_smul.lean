-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.bnd_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:12.989027+00:00
-- url     : https://prove2.me/submissions/aa399cee-b77c-4bc6-b7ce-80bad7bef79d

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt

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
theorem _root_.solution {B : ℝ} (a : ℚ_[p]) {u : MvPolynomial σ ℚ_[p]} (h : Bnd B u) :
    Bnd (‖a‖ * B) (a • u) := by

  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (h m) (norm_nonneg _)
end Formalism.GM.M.PhiIntegrality
