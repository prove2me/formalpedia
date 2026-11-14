-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T19:10:30.483188+00:00
-- url     : https://prove2.me/submissions/c6033112-347f-4b05-9d5b-823420f7ce5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Current-checker revalidation of BVA30 original BV signed error centering reduction after candidate 36719 rejected as stale locally by checker version change. -/
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
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ M : Ω → ℝ, Integrable (F n) P ∧ Integrable M P ∧
        (∫ ω, M ω ∂P) ≤ 0 ∧
        (∀ᵐ ω ∂P, F n ω ≤ w x + M ω + ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n ε hε
  have hFI : Integrable (F n) P :=
    avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite n
  obtain ⟨J, B, R, hJI, hBI, hRI, hJmean, hBmean,
      hRnonneg, hRmean, hFdom⟩ :=
    avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hInfinite
      n ε hε
  let a : ℝ := ∫ ω, R ω ∂P
  let M : Ω → ℝ := fun ω => (J ω + B ω) + (R ω - a)
  have hCentreI : Integrable (fun ω => R ω - a) P :=
    hRI.sub (integrable_const _)
  have hMI : Integrable M P := (hJI.add hBI).add hCentreI
  have hCentre : (∫ ω, R ω - a ∂P) = 0 := by
    rw [integral_sub hRI (integrable_const _)]
    simp [a]
  have hMmean : (∫ ω, M ω ∂P) ≤ 0 := by
    have hSplit :
        (∫ ω, (J ω + B ω) + (R ω - a) ∂P) =
          (∫ ω, J ω + B ω ∂P) +
            (∫ ω, R ω - a ∂P) := by
      exact integral_add (hJI.add hBI) hCentreI
    have hJBSplit :
        (∫ ω, J ω + B ω ∂P) =
          (∫ ω, J ω ∂P) + (∫ ω, B ω ∂P) := by
      exact integral_add hJI hBI
    calc
      (∫ ω, M ω ∂P) =
          (∫ ω, J ω + B ω ∂P) +
            (∫ ω, R ω - a ∂P) := hSplit
      _ = (∫ ω, J ω ∂P) + (∫ ω, B ω ∂P) := by
          rw [hJBSplit, hCentre]
          ring
      _ ≤ 0 := by
          rw [hJmean]
          simpa using hBmean
  refine ⟨M, hFI, hMI, hMmean, ?_⟩
  filter_upwards [hFdom] with ω hUpper
  change F n ω ≤ w x + M ω + ε
  have ha : a ≤ ε := hRmean
  dsimp [M]
  linarith
