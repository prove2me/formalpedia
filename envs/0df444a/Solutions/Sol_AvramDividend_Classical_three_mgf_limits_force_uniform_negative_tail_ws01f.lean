-- Prove2me | solution 1 for AvramDividend.Classical.three_mgf_limits_force_uniform_negative_tail_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:03:58.922993+00:00
-- url     : https://prove2.me/submissions/78d0515c-e099-48d1-a2f0-8ebfc7a4ea4d

import Theorems.Thm_AvramDividend_Classical_three_mgf_negative_probability_integral_bound_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (Y : ℕ → Ω → ℝ) (r : ℝ) (hr : 1 ≤ r)
    (hY : ∀ n, Measurable (Y n))
    (h1 : ∀ n, Integrable (fun ω => Real.exp (Y n ω)) μ)
    (hs : ∀ n, Integrable (fun ω => Real.exp (Y n ω / r)) μ)
    (h2 : ∀ n, Integrable (fun ω => Real.exp (2 * Y n ω)) μ)
    (a b c : ℝ)
    (ha : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (Y n ω) - 1) ∂μ) atTop (nhds a))
    (hb : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (Y n ω / r) - 1) ∂μ) atTop (nhds b))
    (hc : Tendsto (fun n : ℕ =>
      ∫ ω, (Real.exp (2 * Y n ω) - 1) ∂μ) atTop (nhds c))
    (hgap : r ^ 2 * b + c / r < a) :
    ∃ p : ℝ, 0 < p ∧
      ∃ N : ℕ, ∀ n ≥ N,
        p ≤ μ.real {ω | Y n ω < 0} := by
  have hpos : 0 < r := by linarith
  have hcoeff : 0 < r ^ 2 + 1 / r := by positivity
  have hlim : Tendsto (fun n : ℕ =>
      (∫ ω, Real.exp (Y n ω) - 1 ∂μ) -
        (r ^ 2 * (∫ ω, Real.exp (Y n ω / r) - 1 ∂μ) +
          (∫ ω, Real.exp (2 * Y n ω) - 1 ∂μ) / r))
      atTop (nhds (a - (r ^ 2 * b + c / r))) := by
    exact ha.sub ((hb.const_mul (r ^ 2)).add (hc.div_const r))
  have hhalf : (a - (r ^ 2 * b + c / r)) / 2 <
      a - (r ^ 2 * b + c / r) := by linarith
  have hevent : ∀ᶠ n : ℕ in atTop,
      (a - (r ^ 2 * b + c / r)) / 2 <
        (∫ ω, Real.exp (Y n ω) - 1 ∂μ) -
          (r ^ 2 * (∫ ω, Real.exp (Y n ω / r) - 1 ∂μ) +
            (∫ ω, Real.exp (2 * Y n ω) - 1 ∂μ) / r) :=
    hlim.eventually (Ioi_mem_nhds hhalf)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨(a - (r ^ 2 * b + c / r)) /
      (2 * (r ^ 2 + 1 / r)), ?_, N, ?_⟩
  · apply div_pos
    · linarith
    · positivity
  · intro n hn
    have hmgf :=
      three_mgf_negative_probability_integral_bound_ws01f
        (Y n) (hY n) r hr (h1 n) (hs n) (h2 n)
    have hstrict := hN n hn
    have hdiv :
        (a - (r ^ 2 * b + c / r)) / (2 * (r ^ 2 + 1 / r)) =
        ((a - (r ^ 2 * b + c / r)) / 2) / (r ^ 2 + 1 / r) := by
      field_simp [ne_of_gt hcoeff] <;> ring
    rw [hdiv]
    apply (div_le_iff₀ hcoeff).2
    nlinarith [hmgf, hstrict]
