-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFRadRedS.contDiff_clm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:44.882993+00:00
-- url     : https://prove2.me/submissions/75d17a88-0307-44d7-8c5d-424817f88718

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFRadRedS
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical
namespace Formalism.FourierDecayAlt.P.NFRadRedS
theorem _root_.solution {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G] :
    ContDiff ℝ ∞ (fun p : (F →L[ℂ] G) × (E →L[ℂ] F) => p.1.comp p.2) := by
  have h := (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := E) (F := F) (G := G)).contDiff (n := ∞)
  exact h.restrict_scalars ℝ
end Formalism.FourierDecayAlt.P.NFRadRedS
