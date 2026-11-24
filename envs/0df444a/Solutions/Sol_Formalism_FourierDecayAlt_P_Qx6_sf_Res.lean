-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.sf_Res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:39.976329+00:00
-- url     : https://prove2.me/submissions/dbe66835-c60b-4a64-a37b-ac3b161cfbea

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cd_gamma
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_smooth_family_restriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_ofC
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hW : WeylLevelElementFacts) (l : Fin r) {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r l.castSucc (UU Dc) Φ) : SmoothFam k r l.succ (UU (stepD l Dc)) (Res k r l Φ) :=
  Qx3.sf_smul (Qx3.sf_ofC (cd_gamma l _) (fun _ hx => hx.1))
    (smooth_family_restriction hW l h (fun _ hx => ⟨hx.1, hx.1, hx.2⟩))
end Formalism.FourierDecayAlt.P.Qx6
