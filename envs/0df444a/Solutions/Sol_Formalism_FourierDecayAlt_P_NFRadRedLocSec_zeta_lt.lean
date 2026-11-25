-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.zeta_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:54:14.612961+00:00
-- url     : https://prove2.me/submissions/6c806b0e-7883-4e21-b058-0abdd40f8d59

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
variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution {g : Q.Mx k r} (hG : 0 < GGl k r z z' g) :
    Tz k r z * Tz k r z' < Complex.normSq (zetaL k r z z' (Fin.last r) g) := by
  have h : 0 < Complex.normSq (zetaL k r z z' (Fin.last r) g) - Tz k r z * Tz k r z' := hG
  linarith
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
