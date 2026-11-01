-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:20:37.910144+00:00
-- url     : https://prove2.me/submissions/2969c1f8-91dd-4ae3-abce-03fe8d4210b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∀ ω, 0 ≤ θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∧
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, hYX, hc, hσ, hν⟩ := levy_rightCont_process X
  let Z : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)
  let B : ℝ≥0 → Ω → ℝ := fun t ω =>
    Real.exp (-(θ * rightLimit D t ω))
  have hZ : Martingale Z 𝓕.rightCont P := by
    have hY := levy_compensated_exponential_martingale Y θ hθ
    simpa [Z, SpectrallyNegativeLevy.ψ, hYX, hc, hσ, hν] using hY
  have hBadapt : Adapted 𝓕.rightCont B := by
    intro t
    exact ((measurable_const.mul
      (dividendStrategy_rightLimit_adapted_rightCont D hD t)).neg).exp
  have hBbound : ∀ t ω, 0 ≤ B t ω ∧ B t ω ≤ 1 := by
    intro t ω
    constructor
    · exact (Real.exp_pos _).le
    · have hDnonneg : 0 ≤ D t ω := by
        have hm := (hD.2.1 ω) (zero_le : (0 : ℝ≥0) ≤ t)
        change D 0 ω ≤ D t ω at hm
        rw [hD.1 ω] at hm
        exact hm
      have hright : 0 ≤ rightLimit D t ω :=
        le_trans hDnonneg (dividendStrategy_le_rightLimit D hD ω t)
      have hle : -(θ * rightLimit D t ω) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg hθ hright)
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hBsm (r : ℝ≥0) : AEStronglyMeasurable (B r) P :=
    ((hBadapt r).mono (𝓕.rightCont.le r) le_rfl).aestronglyMeasurable
  have hBnorm (r : ℝ≥0) :
      ∀ᵐ ω ∂P, ‖B r ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hBbound r ω).1]
    exact (hBbound r ω).2
  have hIntProd (r v : ℝ≥0) :
      Integrable (fun ω => B r ω * Z v ω) P :=
    (hZ.integrable v).bdd_mul (hBsm r) (hBnorm r)
  have hTermInt (i : ℕ) :
      Integrable (fun ω =>
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) P := by
    have h := (hIntProd (u i) (u (i + 1))).sub
      (hIntProd (u (i + 1)) (u (i + 1)))
    have heq : (fun ω =>
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) =
        (fun ω => B (u i) ω * Z (u (i + 1)) ω -
          B (u (i + 1)) ω * Z (u (i + 1)) ω) := by
      funext ω
      ring
    rw [heq]
    exact h
  have hGridInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω)) P := by
    apply integrable_finset_sum
    intro i hi
    exact hTermInt i
  have hcell (ω : Ω) (i : ℕ) :
      θ * (Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ≤
      Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) := by
    have hm := avram_wave3_03_dividendStrategy_rightLimit_monotone
      D hD ω (hu (Nat.le_succ i))
    have hconv :=
      avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
        θ (rightLimit D (u i) ω) (rightLimit D (u (i + 1)) ω) hθ hm
    have hscaled := mul_le_mul_of_nonneg_left hconv
      (Real.exp_pos (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ)).le
    dsimp [Z, B]
    nlinarith
  have hpositive (ω : Ω) :
      0 ≤ θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) := by
    apply mul_nonneg hθ
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · exact sub_nonneg.mpr
        (avram_wave3_03_dividendStrategy_rightLimit_monotone
          D hD ω (hu (Nat.le_succ i)))
  have hpoint (ω : Ω) :
      θ * ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * B (u (i + 1)) ω *
          (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ≤
      ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hcell ω i
  have hbudget := (avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
    X D hD θ hθ u hu n).2
  change (∀ ω, 0 ≤ θ * ∑ i ∈ Finset.range n,
      Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∧
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤
    (∫ ω, B (u 0) ω * Z (u 0) ω ∂P)
  refine ⟨hpositive, ?_⟩
  calc
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Z (u (i + 1)) ω * B (u (i + 1)) ω *
        (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤
      (∫ ω, ∑ i ∈ Finset.range n,
        Z (u (i + 1)) ω * (B (u i) ω - B (u (i + 1)) ω) ∂P) :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall hpositive) hGridInt
        (Filter.Eventually.of_forall hpoint)
    _ ≤ (∫ ω, B (u 0) ω * Z (u 0) ω ∂P) := hbudget
