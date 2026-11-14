-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb69_original_topcap_physical_strict_F_all_rows_common_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:57:36.535424+00:00
-- url     : https://prove2.me/submissions/2e2ef6a8-3a9a-4a38-9cf3-59d8467427e8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (q : ℝ) (hq : 0 < q) (T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ G : Ω → ℝ, Integrable G P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ G ω := by
  intro δ S F
  let Q : Ω → ℝ := fun ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let R : Ω → ℝ := fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  let G : Ω → ℝ := fun ω => Q ω + R ω
  refine ⟨G, ?_, ?_⟩
  · exact avram_p3_bv_original_prebudget_L1
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) T (le_of_lt hT)
  intro n
  filter_upwards [] with ω
  have hFiniteCash := avram_limit2_original_strict_discounted_cash_finite_all_paths
    X q (le_of_lt hq) x D hD.1.1 ω T (le_of_lt hT)
  have hδ : 0 ≤ δ n := by
    dsimp [δ]
    positivity
  have hCashLe : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ Q ω := by
    change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    apply ENNReal.toReal_mono hFiniteCash
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (sub_le_self T hδ)⟩
  have hTermNonneg : 0 ≤ R ω := by
    dsimp [R]
    split_ifs with hs
    · apply mul_nonneg (le_of_lt (Real.exp_pos _))
      apply hw_nonneg ω S
      · change (0 : ℝ) < T
        exact hT
      · exact hs
    · exact le_refl 0
  have hFNonneg : 0 ≤ F n ω := by
    change 0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + R ω
    exact add_nonneg ENNReal.toReal_nonneg hTermNonneg
  have hFLeG : F n ω ≤ G ω := by
    change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal + R ω ≤ Q ω + R ω
    exact add_le_add hCashLe (le_refl (R ω))
  simpa only [Real.norm_eq_abs, abs_of_nonneg hFNonneg] using hFLeG
