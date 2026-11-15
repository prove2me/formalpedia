-- Prove2me | solution 3 for AvramDividend.Classical.avram_a19_finite_cap_original_full_T_HJB_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:01:45.035206+00:00
-- url     : https://prove2.me/submissions/820a2069-cd54-4ae2-a141-1826f12f6f91
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_finitecap_original_strict_physical_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_strict_prefix_margin_sequence
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- Full T finite-cap original stopped expected reward from physical strict
   prefixes via nonnegative dominated convergence. The sole stochastic
   input is the independent finite-cap HJB physical expected source. -/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x := by
  classical
  intro S
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let Term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Term ω
  let Full : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Term ω
  obtain ⟨hδpos, hδle, hδanti, hδlim⟩ :=
    avram_p3_grid3_strict_prefix_margin_sequence T hTpos
  have hFI : ∀ n, Integrable (F n) P := by
    simpa only [F, δ, Term, S] using
      (avram_bvb62_original_all_cap_strict_cash_plus_full_T_terminal_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hTpos)
  obtain ⟨K, hKI, hK⟩ :=
    avram_bvb_phys60_original_finitecap_uniform_strict_cash_terminal_envelope
      X q hq.le w C hFinite hw_cont hw_neg x hxc D hD T hTpos
  have hKdom : ∀ n ω, F n ω ≤ K ω := by
    simpa only [F, δ, Term, S] using hK
  have hSpos : (0 : ℝ≥0) < S := by
    change (0 : ℝ) < T
    exact hTpos
  have hFpos : ∀ n ω, 0 ≤ F n ω := by
    intro n ω
    have hc : 0 ≤ (∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal :=
      ENNReal.toReal_nonneg
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · dsimp [F, Term]
      rw [if_pos hs]
      exact add_nonneg hc
        (mul_nonneg (Real.exp_pos _).le (hw_nonneg ω S hSpos hs))
    · dsimp [F, Term]
      rw [if_neg hs, add_zero]
      exact hc
  have hDom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ K ω := by
    intro n
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFpos n ω)] using hKdom n ω
  have hLim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (Full ω)) := by
    filter_upwards [] with ω
    have hc :=
      avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
        X x C D hD ω q hq.le T hTpos δ hδpos hδanti hδlim
    simpa only [F, Full] using hc.add (tendsto_const_nhds (x := Term ω))
  have hTend : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop
      (𝓝 (∫ ω, Full ω ∂P)) :=
    tendsto_integral_of_dominated_convergence K
      (fun n => (hFI n).aestronglyMeasurable) hKI hDom hLim
  have hBudget : ∀ n, (∫ ω, F n ω ∂P) ≤ w x := by
    simpa only [F, δ, Term, S] using
      (avram_bv_finitecap_original_strict_physical_expected_cash_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos hFinite)
  have hFull : (∫ ω, Full ω ∂P) ≤ w x :=
    le_of_tendsto hTend (Filter.Eventually.of_forall hBudget)
  simpa only [Full, Term, S] using hFull
