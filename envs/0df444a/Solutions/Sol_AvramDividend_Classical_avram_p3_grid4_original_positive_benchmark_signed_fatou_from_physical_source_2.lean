-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:46:40.663143+00:00
-- url     : https://prove2.me/submissions/4b93e113-1a3a-45aa-b1ed-f1db0bea05f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original BV physical meshes give the positive-benchmark signed Fatou family. -/
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
    (hwpos : 0 < w x) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ F M B : ℕ → Ω → ℝ,
      (∀ n, Measurable (F n)) ∧ (∀ n, Integrable (F n) P) ∧
      (∀ n, 0 ≤ᵐ[P] F n) ∧
      (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + (M n ω + B n ω)) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        ENNReal.ofReal (
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0)) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  have hp : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hl : ∀ n, δ n ≤ T := by
    intro n
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg (le_of_lt hTpos) hn]
  have ha : Antitone δ := by
    intro i j hij
    dsimp [δ]
    apply div_le_div_of_nonneg_left (le_of_lt hTpos) (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 2
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds
  have hz : Tendsto δ atTop (nhds (0 : ℝ)) := by
    simpa only [δ] using (tendsto_const_nhds.div_atTop hden :
      Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (nhds (0 : ℝ)))
  let S : ℝ≥0 := ⟨T, hT⟩
  let F : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  let Y : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨hF, hFatou⟩ :
      (∀ n, Measurable (F n) ∧ Integrable (F n) P ∧ (∀ ω, 0 ≤ F n ω)) ∧
      (∀ ω, ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
    simpa only [F, Y, S, δ] using
      (avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
        X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq)
        T hTpos hw_nonneg δ hp hl ha hz)
  obtain ⟨M, B, E, hR, hEi, hE0, hBound⟩ :
      ∃ M B E : ℕ → Ω → ℝ,
        (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
          (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (E n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (E n ω) 0 ∂P) atTop (nhds 0) ∧
        (∀ n, ∀ᵐ ω ∂P, F n ω ≤
          w x + (M n ω + B n ω) + max (E n ω) 0) := by
    simpa only [F, S, δ] using
      (avram_p3_grid4_original_source_vanishing_mean_physical_cells
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos)
  obtain ⟨F', M', B', hFM, hMR, hRbound, hFlim⟩ :
      ∃ F' M' B' : ℕ → Ω → ℝ,
        (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧ 0 ≤ᵐ[P] F' n) ∧
        (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
          (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
        (∀ n, ∀ᵐ ω ∂P, F' n ω ≤ w x + (M' n ω + B' n ω)) ∧
        (∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
    apply avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
      P (w x) hwpos Y F M B (fun n ω => max (E n ω) 0)
    · exact fun n => (hF n).1
    · exact fun n => (hF n).2.1
    · intro n; filter_upwards [] with ω; exact (hF n).2.2 ω
    · exact hR
    · exact hEi
    · intro n; filter_upwards [] with ω; exact le_max_right _ _
    · exact hE0
    · exact hBound
    · filter_upwards [] with ω; exact hFatou ω
  exact ⟨F', M', B', (fun n => (hFM n).1),
    (fun n => (hFM n).2.1), (fun n => (hFM n).2.2),
    hMR, hRbound, by simpa only [Y, S] using hFlim⟩
