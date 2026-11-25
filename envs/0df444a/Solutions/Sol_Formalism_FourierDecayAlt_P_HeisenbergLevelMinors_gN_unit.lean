-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.gN_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:15.032679+00:00
-- url     : https://prove2.me/submissions/db8c4e99-6357-44e2-9e11-b9ad79728d69

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution {X : Mat k r} (hX : ∀ i j, ‖X i j‖ ≤ 1) : gN X ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
  have hg : gN X = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := rfl
  have h1 : ∀ i j, Complex.normSq (X i j) ≤ 1 := fun i j => by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hX i j, norm_nonneg (X i j)]
  have hs : (∑ i, ∑ j, Complex.normSq (X i j)) ≤
      ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
    calc (∑ i, ∑ j, Complex.normSq (X i j))
        ≤ ∑ _i : Fin (2 * r + k + 1), ∑ _j : Fin (2 * r + k + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hg]
  calc Real.sqrt _ ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ)) :=
        Real.sqrt_le_sqrt hs
    _ = _ := Real.sqrt_mul_self (Nat.cast_nonneg _)
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
