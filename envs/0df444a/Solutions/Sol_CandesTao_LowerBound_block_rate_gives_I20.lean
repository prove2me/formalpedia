-- Prove2me | solution 1 for CandesTao.LowerBound.block_rate_gives_I20
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:23:29.138234+00:00
-- url     : https://prove2.me/submissions/2d26efe5-1419-44f8-9272-e31f7779e2b8

import Definitions.Def_CandesTao_LowerBound_SamplingConditions

namespace CandesTao.LowerBound

theorem aux_brI20_main
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (h : (1 - (m : ℝ) / (n : ℝ) ^ 2) ^ ℓ ≤ 2 * δ / n) :
    SamplingConditionI20 n m r μ₀ δ := by
  unfold SamplingConditionI20
  have hn1 : 1 ≤ n := le_trans hr hrn
  have hn : (0 : ℝ) < n := by exact_mod_cast hn1
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hμr : 0 < μ₀ * r := mul_pos (by linarith) hr'
  have hℓpos : (0 : ℝ) < ℓ := by rw [hℓ]; exact div_pos hn hμr
  have hℓne : ℓ ≠ 0 := by
    intro h0; rw [h0] at hℓpos; simp at hℓpos
  have hkey : (ℓ : ℝ) * (μ₀ * r / n) = 1 := by
    rw [hℓ]; field_simp
  set L := Real.log (n / (2 * δ)) with hL
  set E := Real.exp (-(μ₀ * r / n) * L) with hE
  have hEpow : E ^ ℓ = 2 * δ / n := by
    rw [hE, ← Real.exp_nat_mul]
    have : (ℓ : ℝ) * (-(μ₀ * r / n) * L) = -L := by
      rw [show (ℓ : ℝ) * (-(μ₀ * r / n) * L) = -((ℓ : ℝ) * (μ₀ * r / n)) * L by ring, hkey]
      ring
    rw [this, Real.exp_neg, hL, Real.exp_log (div_pos hn (by linarith))]
    field_simp
  have hEpos : 0 < E := Real.exp_pos _
  have hq : 1 - (m : ℝ) / (n : ℝ) ^ 2 ≤ E := by
    by_cases hq0 : 1 - (m : ℝ) / (n : ℝ) ^ 2 ≤ 0
    · exact le_trans hq0 hEpos.le
    · replace hq0 := not_le.mp hq0
      rw [← pow_le_pow_iff_left₀ hq0.le hEpos.le hℓne, hEpow]
      exact h
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have h2 : (n : ℝ) ^ 2 * (1 - (m : ℝ) / (n : ℝ) ^ 2) ≤ (n : ℝ) ^ 2 * E :=
    mul_le_mul_of_nonneg_left hq hn2.le
  have h3 : (n : ℝ) ^ 2 * (1 - (m : ℝ) / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 - m := by
    field_simp
  rw [h3] at h2
  show (n : ℝ) ^ 2 * (1 - E) ≤ m
  nlinarith

end CandesTao.LowerBound

open CandesTao.LowerBound

theorem solution
    (n m r : ℕ) (μ₀ δ : ℝ) (ℓ : ℕ)
    (hm : 1 ≤ m) (hr : 1 ≤ r) (hrn : r ≤ n) (hμ₀ : 1 ≤ μ₀)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hℓ : (ℓ : ℝ) = n / (μ₀ * r))
    (h : (1 - (m : ℝ) / (n : ℝ) ^ 2) ^ ℓ ≤ 2 * δ / n) :
    SamplingConditionI20 n m r μ₀ δ :=
  aux_brI20_main n m r μ₀ δ ℓ hm hr hrn hμ₀ hδ hδ' hℓ h
