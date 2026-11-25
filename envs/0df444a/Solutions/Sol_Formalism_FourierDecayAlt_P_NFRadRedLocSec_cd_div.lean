-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:28.661118+00:00
-- url     : https://prove2.me/submissions/21b2ff4f-ced6-4eb4-b016-0d85fcbe2453

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
theorem _root_.solution {f g : X → ℂ} (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s) (h0 : ∀ x ∈ s, g x ≠ 0) :
    ContDiffOn ℝ n (fun x => f x / g x) s := by
  have hinv : ContDiffOn ℝ n (fun x => (g x)⁻¹) s := fun x hx =>
    (contDiffAt_inv ℝ (h0 x hx)).comp_contDiffWithinAt x (hg x hx)
  simpa only [div_eq_mul_inv] using hf.mul hinv
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
