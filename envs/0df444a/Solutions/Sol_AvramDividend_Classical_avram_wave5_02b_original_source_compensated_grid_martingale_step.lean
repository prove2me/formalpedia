-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_original_source_compensated_grid_martingale_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:08:19.558201+00:00
-- url     : https://prove2.me/submissions/4937aba4-58da-42d1-a67a-bc1e21912965

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ)
    (ν : Measure ℝ) (f : ℕ → ℝ → ℝ) (rate : ℕ → ℝ)
    (H Z : ℕ → Ω → ℝ)
    (hZsource : ∀ i ω, Z i ω =
      (∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i p.2 ∂(NX ω)) - rate i * ∫ z, f i z ∂ν)
    (J : ℕ → (ℝ≥0 → ℝ) → ℝ) (hJ : ∀ i, Measurable (J i))
    (hRep : ∀ i ω, J i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = Z i ω)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hZi : ∀ i, Integrable (Z i) P)
    (hZ2i : ∀ i, Integrable (fun ω => Z i ω ^ 2) P)
    (hProd : ∀ i, Integrable (H i * Z i) P)
    (hCenter : ∀ i, (∫ ω, Z i ω ∂P) = 0)
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, H j ω * Z j ω))
    (hPrefixI : ∀ i, Integrable
      (fun ω => ∑ j ∈ Finset.range i, H j ω * Z j ω) P)
    (hSigma : ∀ i, @SigmaFinite Ω (𝓕 (grid i))
      (P.trim (𝓕.le (grid i))))
    (n : ℕ) :
    P[(fun ω => ∑ i ∈ Finset.range (n + 1),
      H i ω * Z i ω) | 𝓕 (grid n)] =ᵐ[P]
        (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) := by
  letI := hSigma n
  have hJi : Integrable
      (fun ω => J n (fun t => X.X (grid n + t) ω - X.X (grid n) ω)) P := by
    simpa only [hRep] using hZi n
  have hJ2i : Integrable
      (fun ω => (J n (fun t => X.X (grid n + t) ω - X.X (grid n) ω)) ^ 2) P := by
    simpa only [hRep] using hZ2i n
  have hc := avram_wave5_02b_original_future_path_conditional_first_second_moments
    X (grid n) (J n) (hJ n) hJi hJ2i
  have hz : P[Z n | 𝓕 (grid n)] =ᵐ[P] fun _ => 0 := by
    simpa only [hRep, hCenter n] using hc.1
  have hstep : P[H n * Z n | 𝓕 (grid n)] =ᵐ[P] fun _ => 0 := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (hH n) (hProd n) (hZi n)
    filter_upwards [hpull, hz] with ω hω hzω
    simp only [Pi.mul_apply, hzω, mul_zero] at hω
    exact hω
  have hpast := condExp_of_stronglyMeasurable
    (𝓕.le (grid n)) (hPrefix n) (hPrefixI n)
  have hadd := condExp_add (hPrefixI n) (hProd n) (𝓕 (grid n))
  have hsum : (fun ω => ∑ i ∈ Finset.range (n + 1), H i ω * Z i ω) =
      (fun ω => ∑ i ∈ Finset.range n, H i ω * Z i ω) + H n * Z n := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_range_succ]
  rw [hsum]
  filter_upwards [hadd, hstep] with ω hω hstepω
  simpa only [Pi.add_apply, hpast, hstepω, add_zero] using hω
