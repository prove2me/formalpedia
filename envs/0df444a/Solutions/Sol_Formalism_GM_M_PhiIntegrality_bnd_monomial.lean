-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.bnd_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:46:39.127134+00:00
-- url     : https://prove2.me/submissions/65db2927-9a13-403d-89ed-4ec03569ab41

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
theorem _root_.solution (m : σ →₀ ℕ) (n : ℕ) : Bnd 1 (monomial m ((n : ℕ) : ℚ_[p])) := by

  classical
  intro m'
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · have := Padic.norm_int_le_one (p := p) (n : ℤ)
    simpa using this
  · simp
end Formalism.GM.M.PhiIntegrality
