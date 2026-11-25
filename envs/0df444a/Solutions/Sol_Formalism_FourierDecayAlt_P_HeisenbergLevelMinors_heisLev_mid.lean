-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.heisLev_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:45:02.667895+00:00
-- url     : https://prove2.me/submissions/7a11ebfb-5bb5-457c-a6bc-a1dbbeb017d0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormBallVolumes
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLevelMinors
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_bvec_lv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lev_mulVec_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
open Formalism.FourierDecayAlt.P.B2x6
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j) = g i j := by
  have hw1 : (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) (iL k r') = 0 := by
    rw [lev_mulVec_L]; exact Pi.single_eq_of_ne (lv_ne_iL j).symm _
  have hw2 : res (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) = g *ᵥ bvec j := by
    rw [lev_mulVec_res, bvec_lv, lift_res]
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j), ← Matrix.mulVec_mulVec]
  calc (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ (ιLev k 1 r' g *ᵥ bvec (lv k r' j))) (lv k r' i)
      = res (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ (ιLev k 1 r' g *ᵥ bvec (lv k r' j))) i := rfl
    _ = (res (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) + (ιLev k 1 r' g *ᵥ bvec (lv k r' j)) (iL k r') • x.1) i := by
        rw [heis_res]
    _ = (g *ᵥ bvec j) i := by rw [hw2, hw1, zero_smul, add_zero]
    _ = g i j := (ent g i j).symm
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
