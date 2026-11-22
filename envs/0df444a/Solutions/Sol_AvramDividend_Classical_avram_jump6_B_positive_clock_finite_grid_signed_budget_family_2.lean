-- Prove2me | solution 2 for AvramDividend.Classical.avram_jump6_B_positive_clock_finite_grid_signed_budget_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:50:43.325647+00:00
-- url     : https://prove2.me/submissions/37d57203-d433-49bf-a566-71379fb97e4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

import Theorems.Thm_AvramDividend_Classical_avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∀ k : ℕ,
      let A : Set Ω := {ω | σ k ω ≠ 0}
      ∃ (M E : ℕ → Ω → ℝ),
        (∀ j, IntegrableOn (M j) A P) ∧
        (∀ j, IntegrableOn (E j) A P) ∧
        (∀ j, (∫ ω in A, M j ω ∂P) = 0) ∧
        (∀ j, ∀ᵐ ω ∂(P.restrict A),
          F k ω ≤ w x + M j ω + E j ω) ∧
        Tendsto (fun j => ∫ ω in A, E j ω ∂P) atTop (𝓝 (0 : ℝ))  := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A
  have hA0 : MeasurableSet[𝓕.rightCont 0] A := by simpa only [A] using (avram_jump6_A_original_positive_clock_event_is_initial_filtration_measurable (σ k) (hσstop k))
  have hA : MeasurableSet A :=
    (MeasurableSpace.le_def.mp (𝓕.rightCont.le 0)) A hA0
  have hSource := avram_oai_original_positive_clock_physical_grid_pathwise_remainder_certificate_public_20261122 X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτstop σ F hσstop hσle hFsource hFI hInfiniteActivity k
  obtain ⟨m, s, t, S, g, H, K, E,
    hst, hS, hNeg, hSν, hH, hBound, hSupport,
    hEI, hUpper, hLimit⟩ := hSource
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let B : ℕ → ℕ → ℝ → Set ℝ := fun j i y => S j i ∩ (g j i) ⁻¹' {y}
  let G : ℕ → ℕ → Ω → ℝ := fun j i ω => ∑ y ∈ (g j i).range, y * ((NX ω (Ioc (s j i) (t j i) ×ˢ B j i y)).toReal - ((((t j i - s j i : ℝ≥0) : ℝ≥0∞) * X.ν (B j i y))).toReal)
  let M : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (m j), (if (σ k ω : WithTop ℝ≥0) ≤ (s j i : WithTop ℝ≥0) then 0 else H j i ω) * G j i ω
  have hCentered : ∀ j, Integrable (M j) P ∧ (∫ ω, M j ω ∂P) = 0 := by
    intro j
    simpa only [M, G, B, NX] using (avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122 X (Finset.range (m j)) (s j) (t j) (hst j) (S j) (hS j) (hNeg j) (hSν j) (g j) (H j) (hH j) (K j) (hBound j) (fun ω => (σ k ω : WithTop ℝ≥0)) (hσstop k))
  have hOff : ∀ j ω, ω ∉ A → M j ω = 0 := by
    intro j ω hω
    change (∑ i ∈ Finset.range (m j), (if (σ k ω : WithTop ℝ≥0) ≤ (s j i : WithTop ℝ≥0) then 0 else H j i ω) * G j i ω) = 0
    apply Finset.sum_eq_zero
    intro i hi
    simp [hSupport j i hi ω hω]
  have hIndicator : ∀ j, A.indicator (M j) = M j := by
    intro j
    funext ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω, hOff j ω hω]
  have hZeroOn : ∀ j, (∫ ω in A, M j ω ∂P) = 0 := by
    intro j
    calc
      (∫ ω in A, M j ω ∂P) = (∫ ω, A.indicator (M j) ω ∂P) := (integral_indicator hA).symm
      _ = (∫ ω, M j ω ∂P) := by rw [hIndicator j]
      _ = 0 := (hCentered j).2
  exact ⟨M, E, (fun j => (hCentered j).1.integrableOn), hEI, hZeroOn, hUpper, hLimit⟩
