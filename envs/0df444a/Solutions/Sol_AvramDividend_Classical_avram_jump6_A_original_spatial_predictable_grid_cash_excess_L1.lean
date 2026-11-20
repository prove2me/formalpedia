-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_spatial_predictable_grid_cash_excess_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:13:49.549696+00:00
-- url     : https://prove2.me/submissions/fab5b4cb-a257-4094-9695-919809edc533
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_one_finite_predictable_grid_cash_excess_any_tolerance


open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped Topology
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w
    {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
    (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
    (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
    w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont
    (fun ω => (ρ ω : WithTop ℝ≥0))) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) (hρclip : ∀ ω, ρ ω ≤
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) (κ : ℕ → Ω → ℝ≥0) (hκexact : ∀ k ω, κ k ω = (min (ρ ω : ℝ≥0∞)
    (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
    (fun ω => (κ k ω : WithTop ℝ≥0))) (H : ℕ → Ω → ℝ) (hHsource : ∀ k ω, H k ω =
    Real.exp (-(q * (κ k ω : ℝ))) * w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω then
    x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ (R Jsmall : ℝ≥0 → Ω → ℝ), (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun j : ℕ =>
    avram_p4_h_gaussian_intrinsic_truncated_residual X j u ω) atTop (𝓝 (R u ω))) →
    (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun j : ℕ =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X j u ω) atTop (𝓝 (Jsmall u ω))) →
    ∀ (k : ℕ) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → ∃ (G J : ℕ → Ω → ℝ),
    (∀ m, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
    (∀ i ∈ S, a i ≤ b i) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
    (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG ∧ 0 ≤ LJ ∧
    (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G m ω =
    ∑ i ∈ S, (if κ k ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) ∧ (∀ ω, J m ω =
    ∑ i ∈ S, (if κ k ω ≤ a i then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a i) ω))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ m, (∫ ω in A ∩ {η : Ω | κ k η ≠ 0},
    max (H k ω - w x - (G m ω + J m ω)) 0 ∂P) ≤ ε)  := by
  classical
  intro R Jsmall hR hJ k A hA
  have hEach (m : ℕ) :=
    avram_jump6_A_original_one_finite_predictable_grid_cash_excess_any_tolerance
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn ρ hρstop hρbound hρclip hFiniteActivity hCfinite
      κ hκexact hκstop H hHsource
      R Jsmall hR hJ k A hA (1 / ((m : ℝ) + 1)) (by positivity)
  choose S a b WG WJ LG LJ hData using hEach
  let G : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m, (if κ k ω ≤ a m i then 0 else WG m i ω) *
      (R (b m i) ω - R (a m i) ω)
  let J : ℕ → Ω → ℝ := fun m ω =>
    ∑ i ∈ S m, (if κ k ω ≤ a m i then 0 else WJ m i ω) *
      (Jsmall (b m i) ω - Jsmall (a m i) ω)
  refine ⟨G, J, ?_, ?_⟩
  · intro m
    obtain ⟨hab, hWG, hWJ, hLG, hLJ, hWGbound,
      hWJbound, hSmall⟩ := hData m
    exact ⟨S m, a m, b m, WG m, WJ m, LG m, LJ m,
      hab, hWG, hWJ, hLG, hLJ, hWGbound, hWJbound,
      (fun _ => rfl), (fun _ => rfl)⟩
  · intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / ε)
    refine ⟨m, ?_⟩
    have hDen : (0 : ℝ) < ((m : ℝ) + 1) := by positivity
    have hBound : (1 : ℝ) / ((m : ℝ) + 1) ≤ ε := by
      apply (div_le_iff₀ hDen).2
      have hMult : 1 < (m : ℝ) * ε :=
        (div_lt_iff₀ hε).1 hm
      nlinarith
    obtain ⟨hab, hWG, hWJ, hLG, hLJ, hWGbound,
      hWJbound, hSmall⟩ := hData m
    have hActual :
        (∫ ω in A ∩ {η : Ω | κ k η ≠ 0},
          max (H k ω - w x - (G m ω + J m ω)) 0 ∂P) ≤
            (1 : ℝ) / ((m : ℝ) + 1) := by
      simpa only [G, J] using hSmall
    exact hActual.trans hBound
