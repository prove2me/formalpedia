-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.bigCell_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:56.538413+00:00
-- url     : https://prove2.me/submissions/e4172f80-6b6d-4129-acaf-7bb0aba7b2ab

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hat_z_of_block3
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_uni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_unitary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_eq_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_inv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_cancel_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_gv_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_unitary_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_wMat_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_mul_hpk_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_of
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (g : B.Mat k (j + ρ)) (hg : g ∈ B.GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    ∃ (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ), Z.det ≠ 0 ∧ γ ∈ B.GV k ρ ∧
      g = (Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x' := by
  obtain ⟨FourierUniquenessMirabolic, WeakApproximationGL, WhittakerVanishingImpliesZero, G21, G22, G23, G31, ContDiffOnLocalExtension, G33, rfl⟩ : ∃ FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33,
      g = blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 := ⟨_, _, _, _, _, _, _, _, _, block3_eta g⟩
  have hg1 : (blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33)ᴴ * Hpk k (j + ρ) * blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 =
      Hpk k (j + ρ) := hg
  have hg2 := unitary_right _ hg1
  have e11 : G31ᴴ * G.wMat j * FourierUniquenessMirabolic + G21ᴴ * Hpk k ρ * G21 + FourierUniquenessMirabolicᴴ * G.wMat j * G31 = 0 := by
    have h := hg1
    rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at h
    simpa using h.1
  have f33 : G33 * G.wMat j * G31ᴴ + ContDiffOnLocalExtension * Hpk k ρ * ContDiffOnLocalExtensionᴴ + G31 * G.wMat j * G33ᴴ = 0 := by
    have h := hg2
    rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at h
    simpa using h.2.2.2.2.2.2.2.2
  have hC : IsUnit G31.det := by
    have : DjU k j ρ (blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33) = (G.wMat j * G31).det := by
      unfold DjU; rw [hat_z_of_block3]
    rw [this, Matrix.det_mul] at hD
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hD)
  obtain ⟨Ci, hCi_def⟩ : ∃ Ci, Ci = G31⁻¹ := ⟨_, rfl⟩
  have hCi : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), Ci * (G31 * X) = X := by
    intro m X; rw [hCi_def, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul]
  have hCi' : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), G31 * (Ci * X) = X := by
    intro m X; rw [hCi_def, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hC, Matrix.one_mul]
  have hCiH : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), G31ᴴ * (Ciᴴ * X) = X := by
    intro m X; rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hCi_def, Matrix.nonsing_inv_mul _ hC,
      Matrix.conjTranspose_one, Matrix.one_mul]
  have hCiH' : ∀ {m : Type} (X : Matrix (Fin j) m ℂ), Ciᴴ * (G31ᴴ * X) = X := by
    intro m X; rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hCi_def, Matrix.mul_nonsing_inv _ hC,
      Matrix.conjTranspose_one, Matrix.one_mul]

  obtain ⟨a', ha'⟩ : ∃ a', a' = Ci * ContDiffOnLocalExtension := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = Ci * G33 := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ, c' = -(Hpk k ρ * a'ᴴ * G.wMat j) := ⟨_, rfl⟩
  obtain ⟨S', hS'_def⟩ : ∃ S', S' = G.wMat j * b' + (1 / 2 : ℂ) • (c'ᴴ * Hpk k ρ * c') := ⟨_, rfl⟩
  have hS' : S'ᴴ = -S' := by
    apply eq_neg_of_add_eq_zero_right
    have h0 : G.wMat j * (Ci * ((G33 * G.wMat j * G31ᴴ + ContDiffOnLocalExtension * Hpk k ρ * ContDiffOnLocalExtensionᴴ + G31 * G.wMat j * G33ᴴ) *
        (Ciᴴ * G.wMat j))) = 0 := by rw [f33]; simp
    rw [← h0, hS'_def, hb', hc', ha']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, hCi, hCiH]
    have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [h2]
    module
  have hRx' : Rn k j ρ (Matrix.of.symm c', skewCoords S') = blk3 1 a' b' 0 1 c' 0 0 1 := by
    rw [rn_of c' S' hS']
    congr 1
    · rw [hc']
      simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul]
    · rw [hS'_def]
      simp only [Matrix.mul_add, Matrix.mul_smul, wMat_mul_wMat_mul]
      module

  obtain ⟨c, hc⟩ : ∃ c : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ, c = -(G21 * Ci) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = -(G.wMat j * cᴴ * Hpk k ρ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = a * c - FourierUniquenessMirabolic * Ci := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S, S = G.wMat j * b + (1 / 2 : ℂ) • (cᴴ * Hpk k ρ * c) := ⟨_, rfl⟩
  have hC1 : Ci * G31 = 1 := by rw [hCi_def]; exact Matrix.nonsing_inv_mul _ hC
  have hC2 : G31 * Ci = 1 := by rw [hCi_def]; exact Matrix.mul_nonsing_inv _ hC
  have hC3 : G31ᴴ * Ciᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hC1, Matrix.conjTranspose_one]
  have hC4 : Ciᴴ * G31ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hC2, Matrix.conjTranspose_one]
  have hS : Sᴴ = -S := by
    apply eq_neg_of_add_eq_zero_right
    have h0 : -(Ciᴴ * ((G31ᴴ * G.wMat j * FourierUniquenessMirabolic + G21ᴴ * Hpk k ρ * G21 + FourierUniquenessMirabolicᴴ * G.wMat j * G31) * Ci)) = 0 := by
      rw [e11]; simp
    rw [← h0, hS_def, hb, ha, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi, hCiH, hCi', hCiH', hC1, hC2, hC3, hC4]
    have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [h2]
    module
  have hRx : Rn k j ρ (Matrix.of.symm c, skewCoords S) = blk3 1 a b 0 1 c 0 0 1 := by
    rw [rn_of c S hS]
    congr 1
    · rw [ha]
    · rw [hS_def]
      simp only [Matrix.mul_add, Matrix.mul_smul, wMat_mul_wMat_mul]
      module
  obtain ⟨product_first_partition, sizeConstantAtParamsWeight, flipOneThree, placeRankTwoOne, TaylorLogMetric, flipTwoThree, BlochKatoReduction, SumRepresentations, ArithmeticCylinders, hm⟩ : ∃ product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders,
      Rn k j ρ (Matrix.of.symm c, skewCoords S) * blk3 FourierUniquenessMirabolic WeakApproximationGL WhittakerVanishingImpliesZero G21 G22 G23 G31 ContDiffOnLocalExtension G33 *
        (Rn k j ρ (Matrix.of.symm c', skewCoords S'))⁻¹ = blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders :=
    ⟨_, _, _, _, _, _, _, _, _, block3_eta _⟩
  have hmU : (blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders)ᴴ * Hpk k (j + ρ) * blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders =
      Hpk k (j + ρ) := by
    have hU := Formalism.QuantumDeterminants.uHGroup _ (Hpk k (j + ρ)) (hpk_det k (j + ρ))
    have h1 := hU.2.1 _ (rn_unitary (Matrix.of.symm c, skewCoords S)) _ hg
    have h2 := hU.2.1 _ h1 _ (hU.2.2 _ (rn_unitary (Matrix.of.symm c', skewCoords S'))).2
    rw [hm] at h2
    exact h2
  have hm2 := hm
  rw [hRx, hRx', uni_inv, block3_mul, block3_mul, block3_eq_iff] at hm2
  obtain ⟨h11, h12, h13, h21, h22, h23, h31, h32, h33⟩ := hm2
  simp at h11 h21 h31 h32 h33
  have hP11 : product_first_partition = 0 := by
    rw [← h11, hb, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hC1]
    abel
  have hP21 : placeRankTwoOne = 0 := by
    rw [← h21, hc]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hC1]
    abel
  have hP32 : SumRepresentations = 0 := by
    rw [← h32, ha']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi']
    abel
  have hP33 : ArithmeticCylinders = 0 := by
    rw [← h33, ha', hb']
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose, wMat_conjTranspose, hpk_herm, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul, wMat_mul_wMat_mul, hpk_mul_hpk_mul, wMat_mul_self, hpk_sq, Matrix.mul_one, Matrix.one_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.conjTranspose_sub, hCi']
    abel
  subst hP11 hP21 hP32 hP33 h31
  have hmU2 := hmU
  rw [block3_conjTranspose, hpkBlocks, block3_mul, block3_mul, block3_eq_iff] at hmU2
  obtain ⟨u11, u12, u13, u21, u22, u23, u31, u32, u33⟩ := hmU2
  simp at u11 u12 u13 u21 u22 u23 u31 u32 u33
  have hW : IsUnit (G31ᴴ * G.wMat j).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact (hC.star).mul (wMat_det j)
  have hP12 : sizeConstantAtParamsWeight = 0 := cancel_left _ _ hW u12
  have hγ : TaylorLogMetric ∈ B.GV k ρ := u22
  have hV : IsUnit (TaylorLogMetricᴴ * Hpk k ρ).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact ((gv_det hγ).star).mul (hpk_det k ρ)
  have hP23 : flipTwoThree = 0 := cancel_left _ _ hV u23
  have hP13 : flipOneThree = (G.wMat j * G31)ᴴ⁻¹ * G.wMat j := by
    rw [Matrix.conjTranspose_mul, wMat_conjTranspose]
    have := congrArg ((G31ᴴ * G.wMat j)⁻¹ * ·) u13
    rw [← this, ← Matrix.mul_assoc (G31ᴴ * G.wMat j)⁻¹ (G31ᴴ * G.wMat j) flipOneThree, Matrix.nonsing_inv_mul _ hW,
      Matrix.one_mul]
  subst hP12 hP23
  have hZ : (G.wMat j * G31).det ≠ 0 := by
    rw [Matrix.det_mul]; exact ((wMat_det j).mul hC).ne_zero
  refine ⟨(Matrix.of.symm c, skewCoords S), (Matrix.of.symm c', skewCoords S'), G.wMat j * G31, TaylorLogMetric, hZ, hγ, ?_⟩
  have hmm : mMap k j ρ (G.wMat j * G31) TaylorLogMetric = blk3 0 0 flipOneThree 0 TaylorLogMetric 0 G31 0 0 := by
    unfold mMap
    rw [hP13, wMat_mul_wMat_mul]
  rw [hmm, ← hm]
  simp only [← Matrix.mul_assoc, rn_inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, rn_inv_mul, Matrix.mul_one]
end Formalism.FourierDecayAlt.P.Ux3
