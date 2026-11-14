-- Prove2me | solution 3 for AvramDividend.Classical.avram_bva57_original_BV_physical_joint_cell_contact_L1_signed_grid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:48:05.64111+00:00
-- url     : https://prove2.me/submissions/e0f67325-2ccc-44bc-a438-eab9ce9411e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
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
    ∃ N ErrCell ErrContact : ℕ → Ω → ℝ,
      (∀ m, Integrable (N m) P ∧ (∫ ω, N m ω ∂P) ≤ 0) ∧
      (∀ m, Integrable (fun ω => max (ErrCell m ω) 0) P) ∧
      (∀ m, Integrable (fun ω => max (ErrContact m ω) 0) P) ∧
      (∀ m, ∀ᵐ ω ∂P, F m ω ≤ w x + N m ω +
        max (ErrCell m ω) 0 + max (ErrContact m ω) 0) ∧
      Tendsto (fun m =>
        ∫ ω, max (ErrCell m ω) 0 + max (ErrContact m ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F
  have hI := avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
    X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hInfinite
  have hE := avram_bva_a55_original_BV_true_horizon_asymptotic_expected_cash_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_neg
    hw_smooth hw_gen hw_grad x hx hxc D hD
    hw_nonneg hjump T hT hInfinite
  have hMean (m : ℕ) : (∫ ω, F m ω ∂P) ≤ w x :=
    avram_bvb54_original_true_horizon_reward_expected_from_asymptotic_same_clock
      X x C D hD w q T hT hI hE m
  let N : ℕ → Ω → ℝ := fun m ω => F m ω - w x
  let ErrCell : ℕ → Ω → ℝ := fun _ _ => 0
  let ErrContact : ℕ → Ω → ℝ := fun _ _ => 0
  refine ⟨N, ErrCell, ErrContact, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨(hI m).sub (integrable_const _), ?_⟩
    have hM : (∫ ω, N m ω ∂P) = (∫ ω, F m ω ∂P) - w x := by
      change (∫ ω, F m ω - w x ∂P) =
        (∫ ω, F m ω ∂P) - w x
      rw [integral_sub (hI m) (integrable_const _)]
      simp
      rfl
    linarith [hMean m]
  · intro m
    simpa [ErrCell] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · intro m
    simpa [ErrContact] using
      (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · intro m
    filter_upwards [] with ω
    dsimp [N, ErrCell, ErrContact]
    simp
  · simpa [ErrCell, ErrContact] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)))
