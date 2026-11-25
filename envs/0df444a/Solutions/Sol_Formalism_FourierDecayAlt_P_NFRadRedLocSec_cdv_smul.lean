-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:30.333085+00:00
-- url     : https://prove2.me/submissions/1ab162c9-8a61-410c-9837-c2bd5f0152d2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
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
theorem _root_.solution {c : X → ℂ} {v : X → Fin m → ℂ} (hc : ContDiffOn ℝ n c s) (hv : ContDiffOn ℝ n v s) :
    ContDiffOn ℝ n (fun x => c x • v x) s := by
  refine contDiffOn_pi.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hc.mul (contDiffOn_pi.1 hv i)
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
