-- Prove2me | solution 2 for AvramDividend.Classical.avram_bvb_original_BV_infinite_activity_expected_inner_reward_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:19:14.123419+00:00
-- url     : https://prove2.me/submissions/120505c4-32f0-4b3e-9b03-68c3a9044e33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
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
    ∀ n : ℕ, (∫ ω, F n ω ∂P) ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n
  have hApprox :=
    avram_bva30_original_infinite_activity_eps_localised_compensated_cash_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite
  have hBound : ∀ ε : ℝ, 0 < ε →
      (∫ ω, F n ω ∂P) ≤ w x + ε := by
    intro ε hε
    obtain ⟨M, hF, hM, hMean, hPath⟩ := hApprox n ε hε
    have hDom : Integrable (fun ω => w x + M ω + ε) P :=
      ((integrable_const (w x)).add hM).add (integrable_const ε)
    calc
      (∫ ω, F n ω ∂P) ≤
          ∫ ω, (w x + M ω + ε) ∂P :=
        integral_mono_ae hF hDom hPath
      _ = w x + (∫ ω, M ω ∂P) + ε := by
        change (∫ ω, ((fun _ : Ω => w x) + M + (fun _ : Ω => ε)) ω ∂P) =
          w x + (∫ ω, M ω ∂P) + ε
        rw [integral_add' ((integrable_const (w x)).add hM) (integrable_const ε)]
        rw [integral_add' (integrable_const (w x)) hM]
        simp
      _ ≤ w x + ε := by linarith
  by_contra hn
  have hlt : w x < (∫ ω, F n ω ∂P) := lt_of_not_ge hn
  have hε : 0 < ((∫ ω, F n ω ∂P) - w x) / 2 := by linarith
  have hB := hBound (((∫ ω, F n ω ∂P) - w x) / 2) hε
  linarith
