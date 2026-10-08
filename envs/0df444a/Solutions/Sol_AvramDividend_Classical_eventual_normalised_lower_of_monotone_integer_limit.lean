-- Prove2me | solution 1 for AvramDividend.Classical.eventual_normalised_lower_of_monotone_integer_limit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T10:38:01.143439+00:00
-- url     : https://prove2.me/submissions/57f7e9cf-fe72-4447-aa31-79e5de87ef87

import Mathlib

open Filter

theorem solution (J : ℝ → ℝ) (c A B q : ℝ)
    (hJmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ → J θ₁ ≤ J θ₂)
    (hJlim : Tendsto (fun n : ℕ => J ((n : ℝ) + 1)) atTop (nhds A))
    (hB : 0 ≤ B) (hd : 0 < c + A) (hq : 0 < q) :
    ∃ θ₀ : ℝ, 0 < θ₀ ∧ ∀ θ : ℝ, θ₀ ≤ θ → q / θ < c + J θ - B / θ := by
  have hhalf : 0 < (c + A) / 2 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hJlim ((c + A) / 2) hhalf
  let n0 : ℕ := max N 1
  have hclose := hN n0 (le_max_left _ _)
  rw [Real.dist_eq, abs_lt] at hclose
  have hbase : 0 < (n0 : ℝ) + 1 := by positivity
  have hJn : (c + A) / 2 < c + J ((n0 : ℝ) + 1) := by linarith
  let θ₀ : ℝ := max ((n0 : ℝ) + 1) (2 * (q + B) / (c + A) + 1)
  refine ⟨θ₀, by positivity, ?_⟩
  intro θ hθ
  have hθ1 : (n0 : ℝ) + 1 ≤ θ := le_trans (le_max_left _ _) hθ
  have hθpos : 0 < θ := by linarith
  have hJle : J ((n0 : ℝ) + 1) ≤ J θ := hJmono _ _ hbase hθ1
  have hbig : 2 * (q + B) / (c + A) < θ := by
    have : 2 * (q + B) / (c + A) + 1 ≤ θ₀ := le_max_right _ _
    linarith
  have hdiv : q + B < ((c + A) / 2) * θ := by
    rw [div_lt_iff₀ hd] at hbig
    linarith
  have hquot : (q + B) / θ < (c + A) / 2 := by
    rwa [div_lt_iff₀ hθpos]
  have : q / θ + B / θ < c + J θ := by
    have hsplit : q / θ + B / θ = (q + B) / θ := by ring
    linarith [hsplit, hquot, hJn, hJle]
  linarith
