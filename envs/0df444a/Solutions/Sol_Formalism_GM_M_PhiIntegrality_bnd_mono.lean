-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.bnd_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:49.030426+00:00
-- url     : https://prove2.me/submissions/1e4aebd1-8212-434e-880f-235554a412a9

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
theorem _root_.solution {B B' : ℝ} {u : MvPolynomial σ ℚ_[p]} (h : Bnd B u) (hB : B ≤ B') : Bnd B' u := fun m => (h m).trans hB
end Formalism.GM.M.PhiIntegrality
