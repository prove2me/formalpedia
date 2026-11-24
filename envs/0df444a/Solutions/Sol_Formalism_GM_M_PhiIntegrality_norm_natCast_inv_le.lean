-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.norm_natCast_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:42.817198+00:00
-- url     : https://prove2.me/submissions/c541cf13-e6d9-4035-8128-86f307d07dac

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
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) :
    ‖((n : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (n.factorization p) := by

  have hp1 : p.Prime := Fact.out
  rw [norm_inv, show ((n : ℚ_[p])) = ((n : ℚ) : ℚ_[p]) by push_cast; rfl, Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat, Nat.factorization_def n hp1]
  push_cast
  simp [padicValRat.of_nat]
end Formalism.GM.M.PhiIntegrality
