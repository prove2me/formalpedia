-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.heisLev_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:13.761877+00:00
-- url     : https://prove2.me/submissions/71896bf0-86d4-42d8-9eea-e4221f4e6383

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_lev_bvec_iL
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_ent
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_heis_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_ne_iL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') (j : Fin (2 * r' + k + 1)) :
    (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r') = x.1 j := by
  have h0 : res (bvec (iL k r')) = 0 := funext fun j => Pi.single_eq_of_ne (lv_ne_iL j) _
  have h1 : bvec (iL k r') (iL k r') = 1 := Pi.single_eq_same _ _
  rw [ent (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' j) (iL k r'), ← Matrix.mulVec_mulVec,
    lev_bvec_iL]
  calc (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) (lv k r' j)
      = res (Formalism.FourierDecayAlt.B2.heis0 k r' x *ᵥ bvec (iL k r')) j := rfl
    _ = (res (bvec (iL k r')) + bvec (iL k r') (iL k r') • x.1) j := by rw [heis_res]
    _ = x.1 j := by rw [h0, h1, one_smul, zero_add]
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
