-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_grid_active_poisson_scaling_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:57:28.96077+00:00
-- url     : https://prove2.me/submissions/95cae767-0a2c-42ae-9031-3da5cc46b26b

import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_grid_active_count_binomial_ws01b

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℕ → ℕ → ℝ≥0)
    (ht : ∀ n : ℕ, Monotone (t n))
    (h : ℕ → ℝ)
    (hgap : ∀ n i : ℕ, i < n →
      (((t n (i + 1) - t n i : ℝ≥0) : ℝ)) = h n)
    (r : ℝ)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) *
      (1 - Real.exp (-(h n * (X.ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 r))
    (k : ℕ) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (t n (i + 1)) ω - X.X (t n i) ω <
            X.drift * (((t n (i + 1) - t n i : ℝ≥0) : ℝ)))).card = k})
      atTop (𝓝 (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) := by
  let p : ℕ → ℝ := fun n =>
    1 - Real.exp (-(h n * (X.ν (Iio (0 : ℝ))).toReal))
  have hr' : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 r) := hr
  have hlimit : Tendsto (fun n : ℕ =>
      (Nat.choose n k : ℝ) * p n ^ k * (1 - p n) ^ (n - k))
      atTop (𝓝 (Real.exp (-r) * r ^ k / (k.factorial : ℝ))) :=
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr'
  have hEq : (fun n : ℕ =>
      P.real {ω : Ω |
        ((Finset.range n).filter (fun i =>
          X.X (t n (i + 1)) ω - X.X (t n i) ω <
            X.drift * (((t n (i + 1) - t n i : ℝ≥0) : ℝ)))).card = k}) =
      (fun n : ℕ =>
        (Nat.choose n k : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) := by
    funext n
    have hbin :=
      bv_actual_grid_active_count_binomial_ws01b
        X hBV hFinite (t n) (ht n) n k (h n) (hgap n)
    simpa [p, sub_sub_cancel_left] using hbin
  rw [hEq]
  exact hlimit
