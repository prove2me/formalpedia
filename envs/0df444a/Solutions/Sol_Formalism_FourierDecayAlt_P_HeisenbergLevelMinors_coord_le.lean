-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.coord_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:15.041263+00:00
-- url     : https://prove2.me/submissions/1d7ee07a-36cf-4c6d-af07-73a75eafa7ca

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_norm_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_heisLev_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_heisLev_corner
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


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
    ‖x‖ ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := by
  have hE : ∀ p q, ‖(Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) p q‖ ≤
      gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := fun p q =>
    (Matrix.norm_entry_le_entrywise_sup_norm _).trans (norm_le_gN _)
  have h0 : 0 ≤ gN (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) := Real.sqrt_nonneg _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
    rw [← heisLev_col x g j]
    exact hE _ _
  · rw [Real.norm_eq_abs, ← heisLev_corner x g]
    refine le_trans ?_ (hE (iF k r') (iL k r'))
    set z := (Formalism.FourierDecayAlt.B2.heis0 k r' x * ιLev k 1 r' g) (iF k r') (iL k r')
    have hz : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_nonneg z.re]
    calc |z.im| = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hz
      _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
