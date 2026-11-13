-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva36_original_BV_cofinal_signed_grid_vanishing_positive_L1_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:17:00.811914+00:00
-- url     : https://prove2.me/submissions/110a4e71-24e7-441b-abed-522925da5ec2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
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
    ∃ J B R : ℕ → Ω → ℝ,
      (∀ m, Integrable (J m) P ∧ (∫ ω, J m ω ∂P) = 0) ∧
      (∀ m, Integrable (B m) P ∧ (∫ ω, B m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (R m) P ∧ ∀ᵐ ω ∂P, 0 ≤ R m ω) ∧
      Tendsto (fun m => ∫ ω, R m ω ∂P) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m, ∀ᵐ ω ∂P,
        F m ω ≤ w x + (J m ω + B m ω) + R m ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F
  obtain ⟨N, hNI, hExcessI, hExcess0⟩ :=
    avram_bva38_original_BV_physical_signed_budget_vanishing_positive_excess
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  refine ⟨(fun _ _ => 0), N,
    (fun m ω => max (F m ω - (w x + N m ω)) 0), ?_, hNI, ?_,
    hExcess0, ?_⟩
  · intro m
    exact ⟨integrable_const 0, by simp⟩
  · intro m
    exact ⟨hExcessI m,
      Filter.Eventually.of_forall (fun ω => le_max_right _ _)⟩
  · intro m
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp
      have hh : F m ω - (w x + N m ω) ≤
          max (F m ω - (w x + N m ω)) 0 := le_max_left _ _
      linarith)
