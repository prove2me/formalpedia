-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:39:42.192799+00:00
-- url     : https://prove2.me/submissions/c76ca4cc-0420-45da-8898-526c9ffd8890

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
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {s : Set X} {m : ℕ}
namespace Formalism.FourierDecayAlt.P.NFRadRedLocSec
theorem _root_.solution {F : X → Matrix (Fin m) (Fin m) ℂ} :
    ContDiffOn ℝ n F s ↔ ∀ i j, ContDiffOn ℝ n (fun x => F x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.1 (contDiffOn_pi.1 h i) j
  · intro h
    exact contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => h i j
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
