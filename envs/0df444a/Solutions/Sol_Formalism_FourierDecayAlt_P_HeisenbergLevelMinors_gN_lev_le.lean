-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.gN_lev_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:03.389829+00:00
-- url     : https://prove2.me/submissions/f107d00e-3f13-4362-93e0-4984f20dbc5d

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_heisLev_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_sum_lv_le

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
theorem _root_.solution (x : Formalism.FourierDecayAlt.B2.HPar k r') (g : Mat k r') :
    gN g ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := by
  have hM := heisLev_mid x g
  show Real.sqrt _ ≤ Real.sqrt _
  apply Real.sqrt_le_sqrt
  calc ∑ i, ∑ j, Complex.normSq (g i j)
      = ∑ i, ∑ j, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) (lv k r' j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM i j]
    _ ≤ ∑ i, ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) q) :=
        Finset.sum_le_sum fun i _ =>
          sum_lv_le (fun q => Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (lv k r' i) q))
            (fun q => Complex.normSq_nonneg _)
    _ ≤ ∑ p, ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q) :=
        sum_lv_le (fun p => ∑ q, Complex.normSq ((Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q))
          (fun p => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _)
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
