-- Prove2me | solution 7 for AvramDividend.Classical.avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:03:00.314824+00:00
-- url     : https://prove2.me/submissions/65687329-de71-4eb0-9c1b-f16bc1e71735
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys23_finite_cap_infinite_activity_original_cell_contact
import Theorems.Thm_AvramDividend_Classical_avram_b20_original_arbitrary_monotone_allgrids_physical_B_nonpositive_ae
import Theorems.Thm_AvramDividend_Classical_avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict11_uniform_B_source_to_strict_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_reward_L1_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_discounted_cash_prefix_finite_mono
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  intro δ S F
  letI : IsProbabilityMeasure P := X.isProbability
  let u : ℕ → ℕ → ℝ≥0 := fun n i => ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have huniform (n i : ℕ) : (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2) := rfl
  have hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1) := by
    intro n i hi; apply NNReal.coe_le_coe.mp
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤ T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    gcongr
    omega
  have hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) := by
    intro n; constructor
    · apply Subtype.ext
      simp [u]
    · change T * ((n + 1 : ℕ) : ℝ) / ((n : ℝ) + 2) = T - T / ((n : ℝ) + 2)
      have hd : (n : ℝ) + 2 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  let B : ℕ → Ω → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    (∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) +
    (let J : ℝ≥0 → ℝ := fun t => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
     let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
     ∑ i ∈ Finset.range (n + 1),
       (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1))))
  have hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0 := by
    filter_upwards [
      avram_b20_original_arbitrary_monotone_allgrids_physical_B_nonpositive_ae
        X hBV q w C hw_gen hw_grad x D u hmono] with ω hω
    intro n
    simpa only [B] using hω n
  have hPre : ∀ᵐ ω ∂P, ∀ n i, Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n (i + 1)) = riskProcess X x D (u n (i + 1)) ω := avram_b20_original_uniform_grid_prejump_equals_riskProcess_ae X x D hD.1.1 T hT u huniform
  have hSource := avram_bv_phys23_finite_cap_infinite_activity_original_cell_contact
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
    u hgrid hmono huniform B (by intro n ω; rfl) hAllB hPre hInfinite
  let Strict : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  have hStrictI : Integrable Strict P := by
    simpa only [Strict] using
      (avram_p3_bv_original_strict_reward_L1_nonnegative
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T
        (le_of_lt hT) hT hw_nonneg).1
  have hFull : (∫ ω, Strict ω ∂P) ≤ w x := by
    simpa only [Strict] using
      (avram_bv_strict11_uniform_B_source_to_strict_expected_upper
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT
        u hgrid hmono huniform B (by intro n ω; rfl) hSource)
  intro n
  have hFI : Integrable (F n) P := by
    simpa only [F, δ, S] using
      (avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite n)
  have hPoint : ∀ ω, F n ω ≤ Strict ω := by
    intro ω
    have hd : 0 ≤ δ n := by dsimp [δ]; positivity
    have hcash := avram_chat24_original_discounted_cash_prefix_finite_mono
      D hD.1.1 ω (ruinTime X x D ω) q (le_of_lt hq)
      (T - δ n) T (le_of_lt hT) (sub_le_self T hd)
    dsimp only [F, Strict]
    linarith
  have hMean := integral_mono hFI hStrictI hPoint
  linarith
