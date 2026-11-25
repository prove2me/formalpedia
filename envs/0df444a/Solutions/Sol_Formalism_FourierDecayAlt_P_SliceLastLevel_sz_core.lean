-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:30.222121+00:00
-- url     : https://prove2.me/submissions/8971fb01-2a11-49ee-9701-8d2bf4f0dfa7

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_norm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_sig_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_sig_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_involution_fixes_middle_basis
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_XX
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_unipotent_diag_entry_szX_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_WX
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_SX
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_WW
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_SW
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_N_SS
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_unipotent_diag_entry_szS_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_gblocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_inv_rows
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_inv_colsX
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_EBp
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_pow_mul_pow_le_pow_mul_pow_of_one_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_entry_bound_mono_exponents
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Frame_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_inv_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_upper_factor_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
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
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution (k s : ℕ) (c : Fin (s + 1) → ℂ) (hc : ∀ a, c a ≠ 0) (Q : ℝ) (hQ2 : 2 ≤ Q)
    (hQr : ((s + 1 : ℕ) : ℝ) ≤ Q) (hQk : ((k + 1 : ℕ) : ℝ) ≤ Q) (hQc : ∀ a, ‖c a‖ ≤ Q) (hQK : 2 * unitriangularFactorConstant c ≤ Q)
    (hQd : (s.factorial : ℝ) / ‖∏ a, c a‖ ≤ Q) {n p : B.Mat k (s + 1)} (hn : n ∈ Nset k (s + 1))
    (hp : p ∈ Nset k (s + 1)) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hG : 1 ≤ B.gN (n⁻¹ * bigCell k (s + 1) c μ * p)) :
    EB n (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB p (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB μ (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (s + 2)) := by
  have hm : n⁻¹ ∈ Nset k (s + 1) := sz_N_inv hn
  obtain ⟨hZ, hSW, hSS, hWX, hXX, hWW⟩ := sz_gblocks hm hp c μ
  set m := n⁻¹ with hmdef
  set g := m * bigCell k (s + 1) c μ * p with hgdef
  set G := B.gN g with hGdef
  set L := m.submatrix (szS k (s + 1)) (szS k (s + 1)) with hLdef
  set U := p.submatrix (szX k (s + 1)) (szX k (s + 1)) with hUdef
  set Z := g.submatrix (szS k (s + 1)) (szX k (s + 1)) with hZdef
  set D := (diagonal c : Matrix (Fin (s + 1)) (Fin (s + 1)) ℂ) with hDdef
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hr : ((s + 1 : ℕ) : ℝ) ≤ Q := hQr
  have eG : ∀ {ι κ : Type} (f : ι → Fin (2 * (s + 1) + k + 1)) (f' : κ → Fin (2 * (s + 1) + k + 1)),
      EB (g.submatrix f f') (Q ^ 0 * G ^ 1) := fun f f' a b => by
    simpa using entry_le_gN g (f a) (f' b)
  have eD : EB D (Q ^ 1 * G ^ 0) := fun a b => by
    simp only [hDdef, diagonal_apply, pow_one, pow_zero, mul_one]
    split_ifs with h
    · subst h; exact hQc a
    · simpa using hQ0

  have hL : ∀ a b, a < b → L a b = 0 := fun a b h => sz_N_SS hm a b h
  have hL1 : ∀ a, L a a = 1 := fun a => unipotent_diag_entry_szS_eq_one hm a
  have hU : ∀ a b, b < a → U a b = 0 := fun a b h => sz_N_XX hp a b h
  have hU1 : ∀ a, U a a = 1 := fun a => unipotent_diag_entry_szX_eq_one hp a
  have eZ : EB (L * D * U) G := by
    rw [← hZ]; intro a b; exact entry_le_gN g _ _
  have hGp : (1 : ℝ) ≤ G ^ (s + 1) := one_le_pow₀ hG
  have eU : EB U (Q ^ 1 * G ^ (s + 1)) := fun i j => by
    have h := upper_factor_bound L U c hc hL hL1 hU hU1 hG0 one_pos hGp eZ i j
    refine h.trans ?_
    have : unitriangularFactorConstant c * ((1 + 1⁻¹) * G ^ (s + 1)) = (2 * unitriangularFactorConstant c) * G ^ (s + 1) := by norm_num; ring
    rw [show (∑ i : Fin (s + 1), ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), c (Fin.castLE i.isLt t)‖) =
      unitriangularFactorConstant c from rfl, this, pow_one]
    exact mul_le_mul_of_nonneg_right hQK (by positivity)
  have eZt : EB (Uᵀ * D * Lᵀ) G := by
    have : Uᵀ * D * Lᵀ = (L * D * U)ᵀ := by
      rw [transpose_mul, transpose_mul, hDdef, diagonal_transpose, Matrix.mul_assoc]
    rw [this]; intro a b; exact eZ b a
  have eL : EB L (Q ^ 1 * G ^ (s + 1)) := fun i j => by
    have h := upper_factor_bound Uᵀ Lᵀ c hc (fun a b h => hU b a h) hU1 (fun a b h => hL b a h) hL1 hG0 one_pos hGp
      eZt j i
    rw [transpose_apply] at h
    refine h.trans ?_
    have : unitriangularFactorConstant c * ((1 + 1⁻¹) * G ^ (s + 1)) = (2 * unitriangularFactorConstant c) * G ^ (s + 1) := by norm_num; ring
    rw [show (∑ i : Fin (s + 1), ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), c (Fin.castLE i.isLt t)‖) =
      unitriangularFactorConstant c from rfl, this, pow_one]
    exact mul_le_mul_of_nonneg_right hQK (by positivity)

  have hdetL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L (fun i j h => hL i j (OrderDual.toDual_lt_toDual.mp h))]
    simp [hL1]
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hU i j h)]
    simp [hU1]
  have hdetZ : Z.det = ∏ a, c a := by
    rw [hZ, det_mul, det_mul, hdetL, hdetU, hDdef, det_diagonal]; ring
  have hZu : IsUnit Z.det := by
    rw [hdetZ]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hc a)
  have eI : EB Z⁻¹ (Q ^ 1 * G ^ s) := by
    have h := inv_entry_le Z (by rw [hZ]; exact eZ)
    simp only [Nat.add_sub_cancel] at h
    refine h.mono ?_
    rw [hdetZ, pow_one, div_eq_mul_inv, mul_assoc, mul_comm (G ^ s), ← mul_assoc, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hQd (by positivity)
  have hIZ : Z⁻¹ * (L * D * U) = 1 := by rw [← hZ]; exact Matrix.nonsing_inv_mul Z hZu
  have hZI : (L * D * U) * Z⁻¹ = 1 := by rw [← hZ]; exact Matrix.mul_nonsing_inv Z hZu
  have hUi : U * Z⁻¹ * L * D = 1 := by
    have : (Z⁻¹ * L * D) * U = 1 := by rw [← hIZ]; simp only [Matrix.mul_assoc]
    have := mul_eq_one_comm.mp this
    simpa only [Matrix.mul_assoc] using this
  have hUi' : Z⁻¹ * L * D * U = 1 := by rw [← hIZ]; simp only [Matrix.mul_assoc]
  have hLi : D * U * Z⁻¹ * L = 1 := by
    have : L * (D * U * Z⁻¹) = 1 := by rw [← hZI]; simp only [Matrix.mul_assoc]
    have := mul_eq_one_comm.mp this
    simpa only [Matrix.mul_assoc] using this
  have hLi' : L * D * U * Z⁻¹ = 1 := hZI

  have hpXW : p.submatrix (szX k (s + 1)) (szW k (s + 1)) =
      U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
    rw [hSW]; simp only [← Matrix.mul_assoc]; rw [hUi, Matrix.one_mul]
  have hpXS : p.submatrix (szX k (s + 1)) (szS k (s + 1)) =
      U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szS k (s + 1)) := by
    rw [hSS]; simp only [← Matrix.mul_assoc]; rw [hUi, Matrix.one_mul]
  have hmWS : m.submatrix (szW k (s + 1)) (szS k (s + 1)) =
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L := by
    rw [hWX]; simp only [Matrix.mul_assoc]; rw [show D * (U * (Z⁻¹ * L)) = D * U * Z⁻¹ * L by
      simp only [Matrix.mul_assoc], hLi, Matrix.mul_one]
  have hmXS : m.submatrix (szX k (s + 1)) (szS k (s + 1)) =
      g.submatrix (szX k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L := by
    rw [hXX]; simp only [Matrix.mul_assoc]; rw [show D * (U * (Z⁻¹ * L)) = D * U * Z⁻¹ * L by
      simp only [Matrix.mul_assoc], hLi, Matrix.mul_one]
  have hμ : μ = g.submatrix (szW k (s + 1)) (szW k (s + 1)) -
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
    rw [hWW, hmWS, hpXW]
    have : g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * D *
        (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
        g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
      rw [show g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * D *
        (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
        g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * (L * D * U * Z⁻¹) *
          g.submatrix (szS k (s + 1)) (szW k (s + 1)) by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this]; abel

  have hnm : n * m = 1 := Matrix.mul_nonsing_inv n (sz_N_unit hn)
  obtain ⟨hn1, hn2⟩ := sz_inv_rows hn hm hnm
  have hnSS : n.submatrix (szS k (s + 1)) (szS k (s + 1)) = D * U * Z⁻¹ := by
    have : n.submatrix (szS k (s + 1)) (szS k (s + 1)) =
        n.submatrix (szS k (s + 1)) (szS k (s + 1)) * (L * (D * U * Z⁻¹)) := by
      rw [show L * (D * U * Z⁻¹) = L * D * U * Z⁻¹ by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this, ← Matrix.mul_assoc, hn1, Matrix.one_mul]
  have hnWS : n.submatrix (szW k (s + 1)) (szS k (s + 1)) =
      -(g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹) := by
    have h1 : n.submatrix (szW k (s + 1)) (szS k (s + 1)) * L = -m.submatrix (szW k (s + 1)) (szS k (s + 1)) :=
      eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hn2)
    have : n.submatrix (szW k (s + 1)) (szS k (s + 1)) =
        n.submatrix (szW k (s + 1)) (szS k (s + 1)) * (L * (D * U * Z⁻¹)) := by
      rw [show L * (D * U * Z⁻¹) = L * D * U * Z⁻¹ by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this, ← Matrix.mul_assoc, h1, hmWS, Matrix.neg_mul]
    congr 1
    rw [show g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * (D * U * Z⁻¹) =
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * (L * D * U * Z⁻¹) by simp only [Matrix.mul_assoc],
      hLi', Matrix.mul_one]
  have hpp : p * p⁻¹ = 1 := Matrix.mul_nonsing_inv p (sz_N_unit hp)
  obtain ⟨hp1, hp2⟩ := sz_inv_colsX hp (sz_N_inv hp) hpp
  have hpiXX : p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) = Z⁻¹ * L * D := by
    have : p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) =
        (Z⁻¹ * L * D * U) * p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) := by rw [hUi', Matrix.one_mul]
    rw [this, Matrix.mul_assoc (Z⁻¹ * L * D), hp1, Matrix.mul_one]
  have hpiXW : p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) =
      -(Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) := by
    have h1 : U * p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) = -p.submatrix (szX k (s + 1)) (szW k (s + 1)) :=
      eq_neg_of_add_eq_zero_left hp2
    have : p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) =
        (Z⁻¹ * L * D * U) * p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) := by rw [hUi', Matrix.one_mul]
    rw [this, Matrix.mul_assoc (Z⁻¹ * L * D), h1, hpXW, Matrix.mul_neg]
    congr 1
    rw [show Z⁻¹ * L * D * (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
      Z⁻¹ * (L * D * U * Z⁻¹) * g.submatrix (szS k (s + 1)) (szW k (s + 1)) by simp only [Matrix.mul_assoc],
      hLi', Matrix.mul_one]

  have hk : ((k + 1 : ℕ) : ℝ) ≤ Q := hQk
  have bXW := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eU eI hr) (eG (szS k (s + 1)) (szW k (s + 1))) hr
  have bXS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eU eI hr) (eG (szS k (s + 1)) (szS k (s + 1))) hr
  have bWS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr) eL hr
  have bmXS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szX k (s + 1)) (szX k (s + 1))) eI hr) eL hr
  have bnSS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eD eU hr) eI hr
  have bnWS := EB_neg (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr)
  have bpiXX := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eI eL hr) eD hr
  have bpiXW := EB_neg (sz_EBp hQ0 hG0 eI (eG (szS k (s + 1)) (szW k (s + 1))) hr)
  have bμ2 := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr)
    (eG (szS k (s + 1)) (szW k (s + 1))) hr
  rw [← hpXW] at bXW
  rw [← hpXS] at bXS
  rw [← hmWS] at bWS
  rw [← hmXS] at bmXS
  rw [← hnSS] at bnSS
  rw [← hnWS] at bnWS
  rw [← hpiXX] at bpiXX
  rw [← hpiXW] at bpiXW
  have hT1 : (1 : ℝ) ≤ Q ^ 5 * G ^ (2 * s + 2) := by
    have := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0) (b := 0) (A := 5) (B := 2 * s + 2) (by omega) (by omega); simpa using this
  have h0T : (0 : ℝ) ≤ Q ^ 5 * G ^ (2 * s + 2) := by linarith
  have hmG : m ∈ B.GV k (s + 1) := sz_N_GV hm
  have hpiG : p⁻¹ ∈ B.GV k (s + 1) := sz_N_GV (sz_N_inv hp)
  have hpinv : (p⁻¹)⁻¹ = p := Matrix.nonsing_inv_nonsing_inv p (sz_N_unit hp)
  have hninv : m⁻¹ = n := Matrix.nonsing_inv_nonsing_inv n (sz_N_unit hn)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i j
    rcases sz_cases i with ⟨a, rfl⟩ | ⟨v, rfl⟩ | ⟨a, rfl⟩ <;> rcases sz_cases j with ⟨b, rfl⟩ | ⟨w, rfl⟩ | ⟨b, rfl⟩
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, sz_sig_X]
      exact (entry_bound_mono_exponents hQ1 hG eL (by omega) (by omega)) b a
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, involution_fixes_middle_basis]
      exact (entry_bound_mono_exponents hQ1 hG bWS (by omega) (by omega)) w a
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bmXS (by omega) (by omega)) b a
    · rw [sz_N_WX hn]; simpa using h0T
    · rw [sz_N_WW hn]; split_ifs <;> simp [hT1, h0T]
    · exact (entry_bound_mono_exponents hQ1 hG bnWS (by omega) (by omega)) v b
    · rw [sz_N_SX hn]; simpa using h0T
    · rw [sz_N_SW hn]; simpa using h0T
    · exact (entry_bound_mono_exponents hQ1 hG bnSS (by omega) (by omega)) a b
  ·
    intro i j
    rcases sz_cases i with ⟨a, rfl⟩ | ⟨v, rfl⟩ | ⟨a, rfl⟩ <;> rcases sz_cases j with ⟨b, rfl⟩ | ⟨w, rfl⟩ | ⟨b, rfl⟩
    · exact (entry_bound_mono_exponents hQ1 hG eU (by omega) (by omega)) a b
    · exact (entry_bound_mono_exponents hQ1 hG bXW (by omega) (by omega)) a w
    · exact (entry_bound_mono_exponents hQ1 hG bXS (by omega) (by omega)) a b
    · rw [sz_N_WX hp]; simpa using h0T
    · rw [sz_N_WW hp]; split_ifs <;> simp [hT1, h0T]
    · rw [← hpinv, sz_norm_inv hpiG, involution_fixes_middle_basis, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bpiXW (by omega) (by omega)) b v
    · rw [sz_N_SX hp]; simpa using h0T
    · rw [sz_N_SW hp]; simpa using h0T
    · rw [← hpinv, sz_norm_inv hpiG, sz_sig_S, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bpiXX (by omega) (by omega)) b a
  ·
    rw [hμ]
    refine (EB_sub (eG (szW k (s + 1)) (szW k (s + 1))) bμ2).mono ?_
    have h1 := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0) (b := 1) (A := 3) (B := s + 2) (by omega) (by omega)
    have h2 := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0 + 1 + 1 + 0 + 1) (b := 1 + s + 1) (A := 3) (B := s + 2) (by omega) (by omega)
    have h3 : Q ^ 3 * G ^ (s + 2) + Q ^ 3 * G ^ (s + 2) ≤ Q ^ 5 * G ^ (s + 2) := by
      have hQ3 : 0 ≤ Q ^ 3 := pow_nonneg hQ0 3
      have hq : 2 * Q ^ 3 ≤ Q ^ 5 := by
        have e5 : Q ^ 5 = Q ^ 2 * Q ^ 3 := by ring
        have hQsq : (2 : ℝ) ≤ Q ^ 2 := by nlinarith
        rw [e5]; exact mul_le_mul_of_nonneg_right hQsq hQ3
      have hg : 0 ≤ G ^ (s + 2) := by positivity
      have := mul_le_mul_of_nonneg_right hq hg
      linarith
    linarith
end Formalism.FourierDecayAlt.P.SliceLastLevel
