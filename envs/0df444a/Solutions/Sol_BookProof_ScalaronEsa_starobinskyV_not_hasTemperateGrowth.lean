-- Prove2me | solution 1 for BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:43:26.633013+00:00
-- url     : https://prove2.me/submissions/5ff13e1c-6f03-4043-bd86-f0cedf22b047

-- Generated from ChapterScalaronCoreEsa.lean — solution of BookProof.ScalaronEsa.starobinskyV_not_hasTemperateGrowth
import Mathlib
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronEsa



open Filter Topology MeasureTheory SchwartzMap


open BookProof.StrichartzWave BookProof.FarisLavine BookProof.Starobinsky
open BookProof.QuantumGravityDensitized BookProof.StoneBridge BookProof.NavierStokesFlow
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    ¬ Function.HasTemperateGrowth (fun phi : ℝ => starobinskyV M alpha phi) := by

  intro hgrow
  obtain ⟨k, C, hC⟩ := hgrow.2 0
  have hbound : ∀ x : ℝ, starobinskyV M alpha x ≤ |C| * (1 + |x|) ^ k := by
    intro x
    have h := hC x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    have h2 : starobinskyV M alpha x ≤ C * (1 + |x|) ^ k := by
      refine le_trans (le_abs_self _) ?_
      simpa [Real.norm_eq_abs] using h
    exact h2.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  set a : ℝ := Real.sqrt (2 / 3) / M with ha_def
  have ha : 0 < a := div_pos (Real.sqrt_pos.mpr (by norm_num)) hM
  set c : ℝ := M ^ 4 / (16 * alpha) with hc_def
  have hc : 0 < c := div_pos (by positivity) (by linarith)
  have hval : ∀ t : ℝ, starobinskyV M alpha (-t) = c * (Real.exp (a * t) - 1) ^ 2 := by
    intro t
    have hexp : -(Real.sqrt (2 / 3)) * (-t) / M = a * t := by
      rw [ha_def]; field_simp
    rw [starobinskyV, hexp, ← hc_def]
    ring
  set B : ℝ := |C| * 2 ^ k with hB_def
  set K : ℝ := c * a ^ (k + 1) / (2 * (Nat.factorial (k + 1))) with hK_def
  have hK : 0 < K := by
    have : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
    rw [hK_def]; positivity
  set t : ℝ := max 1 (max (Real.log 2 / a) (B / K + 1)) with ht_def
  have ht1 : (1 : ℝ) ≤ t := le_max_left _ _
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have htlog : Real.log 2 / a ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htB : B / K + 1 ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have hE2 : (2 : ℝ) ≤ Real.exp (a * t) := by
    have hlog : Real.log 2 ≤ a * t := by
      rw [div_le_iff₀ ha] at htlog; linarith [htlog]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (a * t) := Real.exp_le_exp.mpr hlog
  have hfac : (a * t) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) ≤ Real.exp (a * t) :=
    Real.pow_div_factorial_le_exp (a * t) (by positivity) (k + 1)
  have hsq : Real.exp (a * t) / 2 ≤ (Real.exp (a * t) - 1) ^ 2 := by nlinarith [hE2]
  have hlow : K * t * t ^ k ≤ starobinskyV M alpha (-t) := by
    rw [hval t]
    have h2 : K * t * t ^ k = c * (((a * t) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ)) / 2) := by
      rw [hK_def]
      have hfpos : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
      field_simp
      ring
    rw [h2]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hc.le) (mul_le_mul_of_nonneg_left hsq hc.le)
    exact div_le_div_of_nonneg_right hfac (by norm_num)
  have hhigh : starobinskyV M alpha (-t) ≤ B * t ^ k := by
    have h1 := hbound (-t)
    have habs : |(-t)| = t := by rw [abs_neg, abs_of_pos ht0]
    rw [habs] at h1
    refine h1.trans ?_
    have h2 : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    calc |C| * (1 + t) ^ k ≤ |C| * (2 * t) ^ k :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = B * t ^ k := by rw [hB_def, mul_pow]; ring
  have hmul : K * t ≤ B := le_of_mul_le_mul_right (by linarith) (pow_pos ht0 k)
  have hfinal : B + K ≤ K * t := by
    have h := mul_le_mul_of_nonneg_left htB hK.le
    rw [mul_add, mul_div_cancel₀ _ hK.ne'] at h
    linarith
  linarith
