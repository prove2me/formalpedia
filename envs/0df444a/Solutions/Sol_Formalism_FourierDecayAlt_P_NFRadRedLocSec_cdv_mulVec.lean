-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:09.962927+00:00
-- url     : https://prove2.me/submissions/5ccd5ef0-cc27-49e3-b593-12a7d706ad21

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_Rep_mul


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
theorem _root_.solution {F : X → Matrix (Fin m) (Fin m) ℂ} (hF : ContDiffOn ℝ n F s) (v : Fin m → ℂ) :
    ContDiffOn ℝ n (fun x => F x *ᵥ v) s := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact ContDiffOn.sum fun j _ => ((cdm_iff.1 hF) i j).mul contDiffOn_const
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
