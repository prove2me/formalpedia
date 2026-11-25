-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.zhat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:38.334881+00:00
-- url     : https://prove2.me/submissions/733e9a09-8879-4e4e-b7a6-1c5b2ca0e504

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x4_herm_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_Hherm
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_symm
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


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
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Zhat k r z' z g⁻¹ = (Zhat k r z z' g)ᴴ := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  unfold Zhat
  have hu := WeylGroupFacts.isUnit_of_uh hg
  calc herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z b) (fvec k r z' a)
      = herm (Hpk k r) (g *ᵥ (g⁻¹ *ᵥ fvec k r z b)) (g *ᵥ fvec k r z' a) := (B2x5.herm_UH _ hg _ _).symm
    _ = herm (Hpk k r) (fvec k r z b) (g *ᵥ fvec k r z' a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    _ = star (herm (Hpk k r) (g *ᵥ fvec k r z' a) (fvec k r z b)) :=
        (B2x4.herm_symm _ (B2x5.Hherm k r) _ _).symm
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
