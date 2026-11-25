-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:12.666788+00:00
-- url     : https://prove2.me/submissions/e42fc957-4053-4504-bd3f-bc2fd0108a82

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cd_star

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
theorem _root_.solution {F : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) :
    ContDiffOn ℝ n (fun x => (F x)ᴴ) s := by
  refine cdm_iff.2 fun i j => ?_
  simp only [Matrix.conjTranspose_apply]
  exact cd_star ((cdm_iff.1 hF) j i)
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
