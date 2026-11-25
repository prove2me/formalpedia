-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HeisenbergLevelMinors.gN_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:40:52.890796+00:00
-- url     : https://prove2.me/submissions/c58981a0-9ac2-4db3-84fd-9f2d33a4575e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_HeisenbergLevelMinors_gN_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
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


section
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
private lemma gN_mul_le_hermitian_curvature (A B : Mat k r) : gN (A * B) ≤ gN A * gN B := by
  have hA : gN A = Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j)) := rfl
  have hB : gN B = Real.sqrt (∑ i, ∑ j, Complex.normSq (B i j)) := rfl
  have hAB : gN (A * B) = Real.sqrt (∑ i, ∑ j, Complex.normSq ((A * B) i j)) := rfl
  have hSA : 0 ≤ ∑ i, ∑ j, Complex.normSq (A i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have entry : ∀ i j, Complex.normSq (∑ l, A i l * B l j) ≤
      (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) := by
    intro i j
    rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l‖ * ‖B l j‖ :=
      (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ => norm_mul _ _))
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => ‖A i l‖) (fun l => ‖B l j‖)
    have h3 : ∀ l, Complex.normSq (A i l) = ‖A i l‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    have h4 : ∀ l, Complex.normSq (B l j) = ‖B l j‖ ^ 2 := fun l => Complex.normSq_eq_norm_sq _
    simp only [h3, h4]
    have h5 : ‖∑ l, A i l * B l j‖ ^ 2 ≤ (∑ l, ‖A i l‖ * ‖B l j‖) ^ 2 := by
      have := norm_nonneg (∑ l, A i l * B l j)
      nlinarith
    exact h5.trans h2
  have hS : (∑ i, ∑ j, Complex.normSq ((A * B) i j)) ≤
      (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
   calc (∑ i, ∑ j, Complex.normSq ((A * B) i j))
      = ∑ i, ∑ j, Complex.normSq (∑ l, A i l * B l j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          congrArg Complex.normSq Matrix.mul_apply
    _ ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (A i l)) * (∑ l, Complex.normSq (B l j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry i j
    _ = (∑ i, ∑ l, Complex.normSq (A i l)) * (∑ j, ∑ l, Complex.normSq (B l j)) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, Complex.normSq (A i j)) * (∑ i, ∑ j, Complex.normSq (B i j)) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (B l j))]
  rw [hA, hB, hAB]
  exact (Real.sqrt_le_sqrt hS).trans (le_of_eq (Real.sqrt_mul hSA _))
section vol
open Formalism.FourierDecayAlt.P.B2x6
variable {k r' : ℕ}
end vol
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
end
end

set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
theorem _root_.solution {g : Mat k r} (hg : g ∈ GV k r) : gN g⁻¹ ≤ gN (Hpk k r) ^ 2 * gN g := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  have h0 : ∀ M : Mat k r, 0 ≤ gN M := fun M => Real.sqrt_nonneg _
  calc gN (Hpk k r * gᴴ * Hpk k r) ≤ gN (Hpk k r * gᴴ) * gN (Hpk k r) := gN_mul_le_hermitian_curvature _ _
    _ ≤ gN (Hpk k r) * gN gᴴ * gN (Hpk k r) :=
        mul_le_mul_of_nonneg_right (gN_mul_le_hermitian_curvature _ _) (h0 _)
    _ = gN (Hpk k r) ^ 2 * gN g := by rw [gN_conjT]; ring
end Formalism.FourierDecayAlt.P.HeisenbergLevelMinors
