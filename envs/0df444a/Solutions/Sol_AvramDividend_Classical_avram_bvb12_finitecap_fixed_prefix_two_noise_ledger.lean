-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb12_finitecap_fixed_prefix_two_noise_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T20:52:07.651752+00:00
-- url     : https://prove2.me/submissions/9934a16d-7527-442a-a5a3-ba830a578112
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb42_original_fixed_cash_prefix_mark_compensated_positive_excess_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys39_original_fullmask_jump_and_intensity_L1_equal_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0
    < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧
    ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
    (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess
    X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapFinite : C ≠ ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n : ℕ, ∃ (M E : ℕ → Ω → ℝ),
      Integrable (F n) P ∧
      (∀ k, Integrable (M k) P) ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, (∫ ω, M k ω ∂P) = 0) ∧
      (∀ k, ∀ᵐ ω ∂P, F n ω ≤ w x + M k ω + E k ω) ∧
      Tendsto (fun k => ∫ ω, E k ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n
  let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
    if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
       (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
       0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t, X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
  let J : ℕ → Ω → ℝ := fun n ω =>
    ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
  let V : ℕ → Ω → ℝ := fun n ω =>
    ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
  let M : ℕ → Ω → ℝ := fun k ω => J k ω - V k ω
  let E : ℕ → Ω → ℝ :=
    fun k ω => max (F n ω - (w x + M k ω)) (0 : ℝ)
  have hJV : ∀ k : ℕ,
      Integrable (J k) P ∧ Integrable (V k) P ∧
        (∫ ω, J k ω ∂P) = (∫ ω, V k ω ∂P) := by
    simpa only [δ, U, H, NX, J, V] using
      avram_bvb_phys39_original_fullmask_jump_and_intensity_L1_equal_mean
        X hBV q (le_of_lt hq) w C hC hCapFinite hw_cont hw_neg
        x D hD T hT hFinite
  have hFI : ∀ j : ℕ, Integrable (F j) P := by
    simpa only [δ, S, F] using
      avram_p3_comp8_original_canonical_strict_prefix_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
  have hEx :=
    avram_bvb42_original_fixed_cash_prefix_mark_compensated_positive_excess_mean_zero
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hT hFinite
      hIntensityPositive hCapFinite
  have hJInt (k : ℕ) : Integrable (J k) P := (hJV k).1
  have hVInt (k : ℕ) : Integrable (V k) P := (hJV k).2.1
  have hMI (k : ℕ) : Integrable (M k) P :=
    (hJInt k).sub (hVInt k)
  have hEI (k : ℕ) : Integrable (E k) P := by
    change Integrable
      (fun ω => max (F n ω - (w x + M k ω)) (0 : ℝ)) P
    have hSub : Integrable
        (fun ω => F n ω - (w x + M k ω)) P := by
      exact (hFI n).sub ((integrable_const (w x)).add (hMI k))
    exact hSub.pos_part
  have hMean (k : ℕ) : (∫ ω, M k ω ∂P) = 0 := by
    change (∫ ω, J k ω - V k ω ∂P) = 0
    rw [integral_sub (hJV k).1 (hJV k).2.1, (hJV k).2.2, sub_self]
  have hUpper (k : ℕ) : ∀ᵐ ω ∂P,
      F n ω ≤ w x + M k ω + E k ω := by
    apply Filter.Eventually.of_forall
    intro ω
    have hb := le_max_left (F n ω - (w x + M k ω)) (0 : ℝ)
    change F n ω ≤ w x + M k ω +
      max (F n ω - (w x + M k ω)) (0 : ℝ)
    linarith
  refine ⟨M, E, hFI n, hMI, hEI, hMean, hUpper, ?_⟩
  simpa only [δ, S, F, U, H, NX, J, V, M, E] using hEx n
