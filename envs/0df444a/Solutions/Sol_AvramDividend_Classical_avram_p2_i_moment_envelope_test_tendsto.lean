-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_envelope_test_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:47:19.394397+00:00
-- url     : https://prove2.me/submissions/9f3894cc-8b42-471a-81aa-9b8a972d3eb4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_approximation_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integral_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integral_poly_error
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_unit_high_moment_le_mass
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_eventual_real_high_moment_mass_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped BigOperators

theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 ≤ z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ)))
    (g : ℝ → ℝ) (hgi : ∀ i, Integrable g (μi i))
    (hgμ : Integrable g μ)
    (happrox : ∀ γ : ℝ, 0 < γ →
      ∃ p : Polynomial ℝ, ∃ K : ℕ,
        ∀ z : ℝ, 0 ≤ z →
          |g z - p.eval z| ≤ γ * (1 + z ^ K)) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  have hOneμ : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    simpa only [pow_zero] using hμ 0
  have hOnei (i : ι) :
      Integrable (fun _ : ℝ => (1 : ℝ)) (μi i) := by
    simpa only [pow_zero] using hi i 0
  have hnonnegμ : ∀ᵐ z ∂μ, 0 ≤ z :=
    hunit_μ.mono (fun z hz => hz.1)
  have hmass_nonneg : 0 ≤ (∫ _ : ℝ, (1 : ℝ) ∂μ) := by
    apply integral_nonneg
    intro z
    norm_num
  let M : ℝ := (∫ _ : ℝ, (1 : ℝ) ∂μ) + 1
  have hM : 0 < M := by dsimp [M]; linarith
  apply AvramDividend.Classical.avram_p2_i_moment_approximation_tendsto
  intro δ hδ
  let γ : ℝ := δ / (4 * M)
  have hγ : 0 < γ := by
    dsimp [γ]
    exact div_pos hδ (by positivity)
  have hγeq : γ * (4 * M) = δ := by
    dsimp [γ]
    field_simp [ne_of_gt hM]
  have hsmall : γ * (2 * M) ≤ δ := by
    nlinarith [hγeq, mul_nonneg (le_of_lt hγ) (le_of_lt hM)]
  obtain ⟨p, K, hpoint⟩ := happrox γ hγ
  have hpμ : Integrable (fun z : ℝ => p.eval z) μ :=
    AvramDividend.Classical.avram_p2_i_moment_polynomial_integrable μ p hμ
  have hpi (i : ι) : Integrable (fun z : ℝ => p.eval z) (μi i) :=
    AvramDividend.Classical.avram_p2_i_moment_polynomial_integrable (μi i) p (hi i)
  have hconv :
      Tendsto (fun i => ∫ z : ℝ, p.eval z ∂μi i) l
        (nhds (∫ z : ℝ, p.eval z ∂μ)) :=
    AvramDividend.Classical.avram_p2_i_moment_polynomial_integral_tendsto
      l μi μ p hi hμ hmom
  have h0event : ∀ᶠ i in l,
      (∫ _ : ℝ, (1 : ℝ) ∂μi i) < M := by
    simpa only [pow_zero, M] using
      (AvramDividend.Classical.avram_p2_i_moment_eventual_real_high_moment_mass_bound
        l μi μ hunit_μ hOneμ 0 (hμ 0) (hmom 0) 1 (by norm_num))
  have hKevent : ∀ᶠ i in l,
      (∫ z : ℝ, z ^ K ∂μi i) < M := by
    simpa only [M] using
      (AvramDividend.Classical.avram_p2_i_moment_eventual_real_high_moment_mass_bound
        l μi μ hunit_μ hOneμ K (hμ K) (hmom K) 1 (by norm_num))
  have hμK :
      (∫ z : ℝ, z ^ K ∂μ) ≤ (∫ _ : ℝ, (1 : ℝ) ∂μ) :=
    AvramDividend.Classical.avram_p2_i_moment_real_unit_high_moment_le_mass
      μ hunit_μ hOneμ K (hμ K)
  refine ⟨(fun i => ∫ z : ℝ, p.eval z ∂μi i),
    (∫ z : ℝ, p.eval z ∂μ), hconv, ?_, ?_⟩
  · filter_upwards [h0event, hKevent] with i h0 hK
    have hErr :=
      AvramDividend.Classical.avram_p2_i_moment_integral_poly_error
        (μi i) g p γ K (hpositive_i i) hpoint (hgi i) (hpi i)
        (hOnei i) (hi i K)
    have hsum :
        (∫ _ : ℝ, (1 : ℝ) ∂μi i) +
          (∫ z : ℝ, z ^ K ∂μi i) ≤ 2 * M := by
      linarith
    have hmult := mul_le_mul_of_nonneg_left hsum (le_of_lt hγ)
    nlinarith
  · have hErr :=
      AvramDividend.Classical.avram_p2_i_moment_integral_poly_error
        μ g p γ K hnonnegμ hpoint hgμ hpμ hOneμ (hμ K)
    have hsum :
        (∫ _ : ℝ, (1 : ℝ) ∂μ) +
          (∫ z : ℝ, z ^ K ∂μ) ≤ 2 * M := by
      dsimp [M]
      linarith
    have hmult := mul_le_mul_of_nonneg_left hsum (le_of_lt hγ)
    nlinarith
