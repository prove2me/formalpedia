-- Prove2me | solution 1 for Formalism.REAL.exp_polarLog_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:11.520139+00:00
-- url     : https://prove2.me/submissions/8113db48-8843-4cfc-9367-d236a331b5c6

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Theorems.Thm_Formalism_REAL_exp_log_of_pos_spectrum
import Theorems.Thm_Formalism_REAL_polarLog_add_self_eq_log
import Theorems.Thm_Formalism_REAL_conjTranspose_mul_self_pos_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    NormedSpace.exp (polarLog g + polarLog g) = gᴴ * g := by
  rw [polarLog_add_self_eq_log]
  obtain ⟨h1, -, h3⟩ := conjTranspose_mul_self_pos_facts hg
  exact exp_log_of_pos_spectrum h1 h3
end Formalism.REAL
