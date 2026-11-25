-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.inWb_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:53:25.431097+00:00
-- url     : https://prove2.me/submissions/27ef0054-71ec-4986-992d-f2ce4e9d22b9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedLocSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution (c : ℂ) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : inWb k r (c • v) := by
  intro i hi
  simp only [Pi.smul_apply, hv i hi, smul_zero]
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
