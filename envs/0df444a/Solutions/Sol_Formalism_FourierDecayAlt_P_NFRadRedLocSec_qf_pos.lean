-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.qf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:46.945854+00:00
-- url     : https://prove2.me/submissions/65dace25-8568-47bc-8360-b6b321de9c50

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_zeta_lt

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
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution (hT : 0 < Tz k r z) {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) : 0 < qf k r z z' g := by
  unfold qf
  exact div_pos (by linarith [zeta_lt hG]) hT
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
