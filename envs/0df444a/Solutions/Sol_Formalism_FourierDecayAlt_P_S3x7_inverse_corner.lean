-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.inverse_corner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:49.121839+00:00
-- url     : https://prove2.me/submissions/8366830d-dda4-428d-a99f-eac830bafa22

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_corner_invariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block11_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block21_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_block31_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_one_block11
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_one_block21
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_one_block31
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_nu_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_eq_zero_of_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_cm_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_cm_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_exists_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {ϖ : o} (hϖ : Irreducible ϖ) {r k : ℕ} (j : Matrix (Idx r k) (Idx r k) o)
    (X : Matrix (Fin r) (Fin r) o) (hj : KppO j) (hX : b31 j = ϖ • X) :
    ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧
      ((b33 j) * Y * (b11 j)).map (IsLocalRing.residue o) = -(X.map (IsLocalRing.residue o)) ∧
      ∀ (l : ℕ) (hl : l ≤ r),
        IsLocalRing.residue o (cm Y l hl) = (-1) ^ l * IsLocalRing.residue o (cm X l hl) := by
  obtain ⟨hdet, hNU⟩ := hj
  obtain ⟨h11, h33, h21, h31, h32, h22⟩ := nu_blocks hNU
  have hJI : j.map (IsLocalRing.residue o) * j⁻¹.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hIJ : j⁻¹.map (IsLocalRing.residue o) * j.map (IsLocalRing.residue o) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have u33 : IsUnit (b33 (j.map (IsLocalRing.residue o))).det := by
    rw [isUpUni_det _ h33]; exact isUnit_one
  have i31 : b31 (j⁻¹.map (IsLocalRing.residue o)) = 0 := by
    have := block31_mul (j.map (IsLocalRing.residue o)) (j⁻¹.map (IsLocalRing.residue o))
    rw [hJI, one_block31, h31, h32] at this
    exact eq_zero_of_mul u33 (by simpa using this.symm)
  have i21 : b21 (j⁻¹.map (IsLocalRing.residue o)) = 0 := by
    have := block21_mul (j.map (IsLocalRing.residue o)) (j⁻¹.map (IsLocalRing.residue o))
    rw [hJI, one_block21, h21, i31] at this
    exact eq_zero_of_mul h22 (by simpa using this.symm)
  have i11 : b11 (j⁻¹.map (IsLocalRing.residue o)) * b11 (j.map (IsLocalRing.residue o)) = 1 := by
    have := block11_mul (j⁻¹.map (IsLocalRing.residue o)) (j.map (IsLocalRing.residue o))
    rw [hIJ, one_block11, h21, h31] at this
    simpa using this.symm
  obtain ⟨Y, hY⟩ := exists_smul hϖ (b31 j⁻¹) i31
  obtain ⟨C, hC⟩ := exists_smul hϖ (b32 j) h32
  have e0 : X * b11 j⁻¹ + C * b21 j⁻¹ + b33 j * Y = 0 := by
    have := block31_mul j j⁻¹
    rw [Matrix.mul_nonsing_inv _ hdet, one_block31, hX, hC, hY, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, ← smul_add] at this
    ext a b
    have h0 := congrFun (congrFun this a) b
    simp only [Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0.symm).resolve_left hϖ.ne_zero
  have e1 : X.map (IsLocalRing.residue o) * b11 (j⁻¹.map (IsLocalRing.residue o)) +
      b33 (j.map (IsLocalRing.residue o)) * Y.map (IsLocalRing.residue o) = 0 := by
    have := congrArg (fun Z => Z.map (IsLocalRing.residue o)) e0
    simp only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
    have i21' : (b21 j⁻¹).map (IsLocalRing.residue o) = 0 := i21
    rw [i21', Matrix.mul_zero, add_zero] at this
    exact this
  have e2 : b33 (j.map (IsLocalRing.residue o)) * Y.map (IsLocalRing.residue o) *
      b11 (j.map (IsLocalRing.residue o)) = -(X.map (IsLocalRing.residue o)) := by
    rw [eq_neg_of_add_eq_zero_right e1, Matrix.neg_mul, Matrix.mul_assoc, i11, Matrix.mul_one]
  refine ⟨Y, hY, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul]; exact e2
  · intro l hl
    rw [cm_map, cm_map, ← cm_neg, ← e2, corner_invariant h33 h11]
end Formalism.FourierDecayAlt.P.S3x7
