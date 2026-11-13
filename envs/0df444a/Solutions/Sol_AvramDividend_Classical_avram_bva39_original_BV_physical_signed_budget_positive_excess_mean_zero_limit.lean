-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva39_original_BV_physical_signed_budget_positive_excess_mean_zero_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:47:26.139316+00:00
-- url     : https://prove2.me/submissions/27db2420-b1d9-45eb-99ea-eab3ae9bf0b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva43_original_BV_physical_signed_two_error_mesh_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∃ N : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      Tendsto (fun m =>
        ∫ ω, max (F m ω - (w x + N m ω)) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F
  obtain ⟨N, ErrCell, ErrContact, hN, hCellI, hContactI,
      hPhysical, hCell0, hContact0⟩ :=
    avram_bva43_original_BV_physical_signed_two_error_mesh_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  have hExI : ∀ m : ℕ, Integrable
      (fun ω => max (F m ω - (w x + N m ω)) 0) P := by
    intro m
    have hi :=
      avram_p3_comp9_original_strict_cash_compensator_positive_excess_L1
        X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
        (fun _ _ => 0) N
        (fun _ => integrable_const (0 : ℝ))
        (fun k => (hN k).1) m
    simpa only [zero_add] using hi
  have hExMeas : ∀ m : ℕ, AEStronglyMeasurable
      (fun ω => max (F m ω - (w x + N m ω)) 0) P :=
    fun m => (hExI m).aestronglyMeasurable
  have hBudget : ∀ m : ℕ, ∀ᵐ ω ∂P,
      F m ω ≤ w x + (0 + N m ω) +
        max (ErrCell m ω) 0 + max (ErrContact m ω) 0 := by
    intro m
    filter_upwards [hPhysical m] with ω hw
    simpa only [zero_add] using hw
  have hGlue :=
    avram_bv_strict10_two_positive_errors_exact_excess_L1_tendsto
      P F (fun _ _ => 0) N ErrCell ErrContact (w x)
      hCellI hContactI
      (by
        intro m
        simpa only [zero_add] using hExMeas m)
      hBudget hCell0 hContact0
  refine ⟨N, hN, ?_⟩
  simpa only [zero_add] using hGlue.2
