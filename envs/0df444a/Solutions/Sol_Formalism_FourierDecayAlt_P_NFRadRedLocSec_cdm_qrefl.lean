-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedLocSec.cdm_qrefl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:39.857645+00:00
-- url     : https://prove2.me/submissions/d1225dfb-4601-4de7-aae7-03f681f2348b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cdm_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFRadRedLocSec_cd_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
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
theorem _root_.solution (H : Matrix (Fin m) (Fin m) ℂ) {d : X → Fin m → ℂ} {c : X → ℂ} (hd : ContDiffOn ℝ n d s)
    (hc : ContDiffOn ℝ n c s) : ContDiffOn ℝ n (fun x => TwoByOneBlock.qrefl H (d x) (c x)) s := by
  refine cdm_iff.2 fun i j => ?_
  simp only [TwoByOneBlock.qrefl, Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.vecMul, dotProduct, Pi.star_apply]
  exact contDiffOn_const.add (hc.mul ((contDiffOn_pi.1 hd i).mul
    (ContDiffOn.sum fun k _ => (cd_star (contDiffOn_pi.1 hd k)).mul contDiffOn_const)))
end Formalism.FourierDecayAlt.P.NFRadRedLocSec
