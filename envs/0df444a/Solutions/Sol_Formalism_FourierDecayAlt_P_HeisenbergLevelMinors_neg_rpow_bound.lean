-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.neg_rpow_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:54:00.860616+00:00
-- url     : https://prove2.me/submissions/a5974d39-eedf-4c6c-8bc3-075143536100

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key


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
theorem _root_.solution {y s c A : ℝ} (hy : 0 < y) (hs : 0 < s) (hc : 0 < c) (hA : 0 < A) (h : y ≤ c * s) :
    s ^ (-A) ≤ c ^ A * y ^ (-A) := by
  have h1 : y ^ A ≤ (c * s) ^ A := Real.rpow_le_rpow hy.le h hA.le
  rw [Real.mul_rpow hc.le hs.le] at h1
  have hsA : 0 < s ^ A := Real.rpow_pos_of_pos hs A
  have hyA : 0 < y ^ A := Real.rpow_pos_of_pos hy A
  have hcA : 0 < c ^ A := Real.rpow_pos_of_pos hc A
  have key : 1 / (c ^ A * s ^ A) ≤ 1 / y ^ A := one_div_le_one_div_of_le hyA h1
  rw [Real.rpow_neg hs.le, Real.rpow_neg hy.le]
  have e1 : (s ^ A)⁻¹ = c ^ A * (1 / (c ^ A * s ^ A)) := by
    field_simp
  rw [e1, ← one_div]
  exact mul_le_mul_of_nonneg_left key hcA.le
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
