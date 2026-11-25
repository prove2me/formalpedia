-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.aux_statement_17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:27:07.365981+00:00
-- url     : https://prove2.me/submissions/0f554e0c-24c3-411a-93a0-bb4fd43bcf1c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_mx_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_mx
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_inv_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_self_le_pow_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block2_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_sizes_unipotent_first
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block2_apply_upper_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_sizes_unipotent_second
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_block2_apply_lower_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_zj_affine
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux5_det_upper__b26aa4d03702
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux5_det_lowW__bdb85a5f13cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_det_permutationMatrix_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_permutationMatrix_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_lowW_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_upper_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_upper_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_upper_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_nat_mul_factorial_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_norm_pi_pi_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_upper_factor_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
namespace _root_.Formalism.FourierDecayAlt.P
theorem _root_.solution : BlockHeadSizes := by
  intro p s σ d hd
  set dH : ℂ := (wP σ).det * ∏ i, d i with hdH
  have hdH0 : dH ≠ 0 := mul_ne_zero (det_permutationMatrix_ne_zero σ) (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  have hdHpos : 0 < ‖dH‖ := norm_pos_iff.mpr hdH0
  have hdetH : ∀ v u, (headH σ d v u).det = dH := by
    intro v u
    unfold headH
    rw [det_mul, det_mul, det_mul, det_upper', det_lowW', det_diagonal]
    ring
  set δ0 : ℝ := ‖dH‖ / (p.factorial : ℝ) with hδ0
  have hδ0pos : 0 < δ0 := by positivity
  set Kd : ℝ := ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖
    with hKd
  have hKd0 : 0 ≤ Kd := Finset.sum_nonneg fun _ _ => by positivity
  have hδi : 0 ≤ δ0⁻¹ := inv_nonneg.mpr hδ0pos.le
  refine ⟨Kd * (1 + δ0⁻¹) + (p.factorial : ℝ) / ‖dH‖ + (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖),
    fun η Z => ?_⟩
  obtain ⟨⟨a, b⟩, ⟨v, u⟩⟩ := η
  set H := headH σ d v u with hH
  set m := mx (ZjH σ d ((a, b), (v, u)) Z) with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hZj : ZjH σ d ((a, b), (v, u)) Z =
      blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + Matrix.of Z) := by
    unfold ZjH
    exact zj_affine _ _ _ _
  have hent : ∀ x y, ‖ZjH σ d ((a, b), (v, u)) Z x y‖ ≤ m := fun x y => entry_le_mx _ x y
  have hHb : EB H m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
    rwa [hZj, sizes_unipotent_first] at this
  have hHBb : EB (H * Matrix.of b) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
    rwa [hZj, block2_apply_upper_right] at this
  have hAHb : EB (Matrix.of a * H) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
    rwa [hZj, sizes_unipotent_second] at this
  have hBRb : EB (Matrix.of a * H * Matrix.of b + Matrix.of Z) m := by
    intro i j
    have := hent (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
    rwa [hZj, block2_apply_lower_right] at this
  have hδm : δ0 ≤ m ^ p := by
    have h := det_norm_le H hHb
    rw [hdetH, Fintype.card_fin] at h
    rw [hδ0, div_le_iff₀ (by positivity)]
    linarith

  set M0 := lowW σ v * diagonal d * G.upper u with hM0
  have hHM : H = wP σ * M0 := by
    simp only [hH, hM0, headH, mul_assoc]
  have hM0b : EB M0 m := by
    intro i j
    have := hHb (σ.symm i) j
    rwa [hHM, permutationMatrix_mul_apply, Equiv.apply_symm_apply] at this
  have hu : ∀ q : G.UT p, ‖u q‖ ≤ Kd * ((1 + δ0⁻¹) * m ^ p) := by
    intro q
    rw [← upper_entry u q]
    exact upper_factor_bound (lowW σ v) (G.upper u) d hd (lowW_lower σ v) (lowW_diag σ v) (upper_upper u)
      (upper_diag u) hm0 hδ0pos hδm hM0b _ _
  have hv : ∀ q : LW σ, ‖v q‖ ≤ Kd * ((1 + δ0⁻¹) * m ^ p) := by
    intro q
    rw [← lowW_entry σ v q]
    have eT : (G.upper u)ᵀ * diagonal d * (lowW σ v)ᵀ = M0ᵀ := by
      rw [hM0, transpose_mul, transpose_mul, diagonal_transpose, mul_assoc]
    have hT : EB ((G.upper u)ᵀ * diagonal d * (lowW σ v)ᵀ) m := by
      intro i j
      rw [eT, transpose_apply]
      exact hM0b j i
    have := upper_factor_bound ((G.upper u)ᵀ) ((lowW σ v)ᵀ) d hd
      (fun a b h => by rw [transpose_apply]; exact upper_upper u b a h)
      (fun a => by rw [transpose_apply]; exact upper_diag u a)
      (fun a b h => by rw [transpose_apply]; exact lowW_lower σ v b a h)
      (fun a => by rw [transpose_apply]; exact lowW_diag σ v a) hm0 hδ0pos hδm hT q.1.2 q.1.1
    rwa [transpose_apply] at this

  have hHu : IsUnit H.det := by rw [hdetH]; exact isUnit_iff_ne_zero.mpr hdH0
  have hHi : EB H⁻¹ ((p - 1).factorial * m ^ (p - 1) / ‖dH‖) := by
    have := inv_entry_le H hHb
    rwa [hdetH] at this
  set bA : ℝ := (p.factorial : ℝ) / ‖dH‖ * m ^ p with hbA
  have hfa := nat_mul_factorial_bound p hm0 hdHpos
  have ha : EB (Matrix.of a) bA := by
    have h1 : Matrix.of a = Matrix.of a * H * H⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hHu, Matrix.mul_one]
    have h2 := EB_mul hAHb hHi
    rw [← h1, Fintype.card_fin] at h2
    exact h2.mono hfa
  have hb : EB (Matrix.of b) bA := by
    have h1 : Matrix.of b = H⁻¹ * (H * Matrix.of b) := by rw [← Matrix.mul_assoc, nonsing_inv_mul _ hHu, Matrix.one_mul]
    have h2 := EB_mul hHi hHBb
    rw [← h1, Fintype.card_fin] at h2
    exact h2.mono ((le_of_eq (by ring)).trans hfa)
  have hbA0 : 0 ≤ bA := by positivity
  have hZb : EB (Matrix.of Z) (m + p * (m * bA)) := by
    have h1 : Matrix.of Z = (Matrix.of a * H * Matrix.of b + Matrix.of Z) - Matrix.of a * H * Matrix.of b := by abel
    have h2 := EB_sub hBRb (EB_mul hAHb hb)
    rwa [← h1, Fintype.card_fin] at h2
  have hself := self_le_pow_succ hm0 hδ0pos hδm
  have hmp : 0 ≤ m ^ p := pow_nonneg hm0 p
  set C := Kd * (1 + δ0⁻¹) + (p.factorial : ℝ) / ‖dH‖ + (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖)
    with hC
  have hC1 : Kd * (1 + δ0⁻¹) ≤ C := by
    have h1 : 0 ≤ (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) := by positivity
    have h2 : 0 ≤ (p.factorial : ℝ) / ‖dH‖ := by positivity
    rw [hC]; linarith
  have hC2 : (p.factorial : ℝ) / ‖dH‖ ≤ C := by
    rw [hC]; have : 0 ≤ (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) := by positivity
    have : 0 ≤ Kd * (1 + δ0⁻¹) := by positivity
    linarith
  have hC3 : (1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) ≤ C := by
    rw [hC]; have : 0 ≤ (p.factorial : ℝ) / ‖dH‖ := by positivity
    have : 0 ≤ Kd * (1 + δ0⁻¹) := by positivity
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show ‖a‖ ≤ C * m ^ p
    refine norm_pi_pi_le a (by positivity) fun i t => (ha i t).trans ?_
    rw [hbA]
    exact mul_le_mul_of_nonneg_right hC2 hmp
  · show ‖b‖ ≤ C * m ^ p
    refine norm_pi_pi_le b (by positivity) fun i t => (hb i t).trans ?_
    rw [hbA]
    exact mul_le_mul_of_nonneg_right hC2 hmp
  · show ‖v‖ ≤ C * m ^ p
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => (hv q).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC1 hmp
  · show ‖u‖ ≤ C * m ^ p
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => (hu q).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hC1 hmp
  · show ‖Z‖ ≤ C * m ^ (p + 1)
    refine norm_pi_pi_le Z (by positivity) fun i t => (hZb i t).trans ?_
    have e : m + p * (m * bA) ≤ ((1 + δ0⁻¹) + (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖)) * m ^ (p + 1) := by
      rw [hbA, add_mul, pow_succ]
      have : (p : ℝ) * (m * ((p.factorial : ℝ) / ‖dH‖ * m ^ p)) =
          (p : ℝ) * ((p.factorial : ℝ) / ‖dH‖) * (m ^ p * m) := by ring
      rw [this]
      rw [pow_succ] at hself
      linarith
    exact e.trans (mul_le_mul_of_nonneg_right hC3 (by positivity))
  ·
    intro hZ0
    have hZu : IsUnit (Matrix.of Z).det := isUnit_iff_ne_zero.mpr hZ0
    have hinv : (ZjH σ d ((a, b), (v, u)) Z)⁻¹ =
        blk2 1 (-(Matrix.of b)) 0 1 * blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹ * blk2 1 0 (-(Matrix.of a)) 1 := by
      apply Matrix.inv_eq_left_inv
      have e1 : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 (-(Matrix.of a)) 1 * blk2 1 0 (Matrix.of a) 1 = 1 := by
        rw [block2_mul]; simp [block2_one]
      have e2 : blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹ * blk2 H 0 0 (Matrix.of Z) = 1 := by
        rw [block2_mul]; simp [nonsing_inv_mul _ hHu, nonsing_inv_mul _ hZu, block2_one]
      have e3 : blk2 (1 : Matrix (Fin p) (Fin p) ℂ) (-(Matrix.of b)) 0 1 * blk2 1 (Matrix.of b) 0 1 = 1 := by
        rw [block2_mul]; simp [block2_one]
      unfold ZjH Zj
      simp only [mul_assoc]
      rw [← mul_assoc (blk2 1 0 (-(Matrix.of a)) 1), e1, one_mul, ← mul_assoc (blk2 H⁻¹ 0 0 (Matrix.of Z)⁻¹), e2,
        one_mul, e3]
    refine mx_le (fun i t => ?_) (norm_nonneg _)
    have e := congrFun (congrFun hinv (finSumFinEquiv (Sum.inr i))) (finSumFinEquiv (Sum.inr t))
    rw [block2_mul, block2_mul, block2_apply_lower_right] at e
    simp at e
    rw [← e]
    exact entry_le_mx _ _ _
end _root_.Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P.Ux5
