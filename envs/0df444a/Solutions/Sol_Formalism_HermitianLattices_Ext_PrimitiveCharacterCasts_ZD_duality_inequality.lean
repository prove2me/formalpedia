-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.duality_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:32.583797+00:00
-- url     : https://prove2.me/submissions/95767e15-4069-4103-a226-e46ee1b3c08f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : DualIneq := by
  intro ι κ S I b v Δ hΔ hrow
  classical
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  obtain ⟨s, hs⟩ : ∃ s : ι → ℂ, s = fun i => ∑ n ∈ I, b n * v i n := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : κ → ℂ, w = fun n => ∑ i ∈ S, (starRingEnd ℂ) (s i) * v i n := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ι → ι → ℂ, G = fun i j => ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) :=
    ⟨_, rfl⟩
  have hs' : ∀ i, ∑ n ∈ I, b n * v i n = s i := fun i => by rw [hs]
  have hG' : ∀ i j, ∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n) = G i j := fun i j => by rw [hG]
  simp_rw [hs']
  simp_rw [hG'] at hrow
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i ∈ S, ‖s i‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ∑ n ∈ I, ‖b n‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX, ← hB]
  have hXnn : 0 ≤ X := by rw [hX]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity

  have h1 : ((X : ℝ) : ℂ) = ∑ n ∈ I, b n * w n := by
    rw [hX, Complex.ofReal_sum]
    simp_rw [hz]
    simp only [hw, Finset.mul_sum]
    conv_lhs => enter [2, i]; rw [hs]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro i _
    rw [hs]
    ring
  have h2 : X ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by
    calc X = ‖((X : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hXnn]
      _ = ‖∑ n ∈ I, b n * w n‖ := by rw [h1]
      _ ≤ ∑ n ∈ I, ‖b n * w n‖ := norm_sum_le _ _
      _ = ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by simp_rw [norm_mul]
  have h3 := Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖b n‖) (fun n => ‖w n‖)

  have hGsym : ∀ i j, ‖G i j‖ = ‖G j i‖ := by
    intro i j
    have e : G j i = (starRingEnd ℂ) (G i j) := by
      rw [hG]
      simp only [map_sum, map_mul, Complex.conj_conj]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [e, Complex.norm_conj]
  have e : ((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j := by
    conv_rhs => rw [Finset.sum_comm]
    rw [Complex.ofReal_sum]
    simp_rw [hz]
    simp only [hw, hG, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm (s := I) (t := S)]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hle : ∑ n ∈ I, ‖w n‖ ^ 2 ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
    have hnn : (0 : ℝ) ≤ ∑ n ∈ I, ‖w n‖ ^ 2 := by positivity
    calc ∑ n ∈ I, ‖w n‖ ^ 2 = ‖((∑ n ∈ I, ‖w n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ = ‖∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := by rw [e]
      _ ≤ ∑ i ∈ S, ‖∑ j ∈ S, (starRingEnd ℂ) (s i) * s j * G i j‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ := by
          apply Finset.sum_le_sum
          intro i _
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_mul, norm_mul, Complex.norm_conj]
  have hsplit : ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) =
      ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => ‖s j‖ ^ 2 * ‖G j i‖ / 2), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hamgm : ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖ ≤ Δ * X := by
    calc ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ * ‖s j‖ * ‖G i j‖
        ≤ ∑ i ∈ S, ∑ j ∈ S, (‖s i‖ ^ 2 * ‖G i j‖ / 2 + ‖s j‖ ^ 2 * ‖G j i‖ / 2) := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [← hGsym i j]
          have h0 := sq_nonneg (‖s i‖ - ‖s j‖)
          have hg := norm_nonneg (G i j)
          nlinarith
      _ = ∑ i ∈ S, ∑ j ∈ S, ‖s i‖ ^ 2 * ‖G i j‖ := hsplit
      _ = ∑ i ∈ S, ‖s i‖ ^ 2 * ∑ j ∈ S, ‖G i j‖ := by simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S, ‖s i‖ ^ 2 * Δ := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg _)
      _ = Δ * X := by rw [hX, Finset.mul_sum]; simp_rw [mul_comm]
  have hXsq : X ^ 2 ≤ B * (Δ * X) := by
    have hY : 0 ≤ ∑ n ∈ I, ‖b n‖ * ‖w n‖ := by positivity
    calc X ^ 2 ≤ (∑ n ∈ I, ‖b n‖ * ‖w n‖) ^ 2 := by nlinarith
      _ ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * ∑ n ∈ I, ‖w n‖ ^ 2 := h3
      _ ≤ B * (Δ * X) := by
          rw [← hB]
          exact mul_le_mul_of_nonneg_left (hle.trans hamgm) hBnn
  rcases hXnn.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
