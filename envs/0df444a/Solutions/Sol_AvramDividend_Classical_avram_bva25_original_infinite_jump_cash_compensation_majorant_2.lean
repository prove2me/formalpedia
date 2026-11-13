-- Prove2me | solution 2 for AvramDividend.Classical.avram_bva25_original_infinite_jump_cash_compensation_majorant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T11:12:27.770327+00:00
-- url     : https://prove2.me/submissions/ce913922-9708-479b-a50b-d0b0e6acf3a7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
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
    ∀ n : ℕ, ∃ M : Ω → ℝ,
      Integrable (F n) P ∧ Integrable M P ∧
      (∫ ω, M ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, F n ω ≤ w x + M ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F n
  have hF : Integrable (F n) P :=
    avram_bva33_original_BV_infinite_activity_inner_cash_terminal_integrable
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hInfinite n
  have hApprox : ∀ ε : ℝ, 0 < ε →
      (∫ ω, F n ω ∂P) ≤ w x + ε := by
    intro ε hε
    obtain ⟨J, B, R, hJi, hBi, hRi, hJ0, hBneg,
        hRpos, hRmean, hBound⟩ :=
      avram_bva34_original_infinite_activity_physical_L1_error_jump_drift_source
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
        x hx hxc D hD hw_nonneg hjump T hT hInfinite n ε hε
    have hJB : Integrable (fun ω => J ω + B ω) P := hJi.add hBi
    have hComp : Integrable (fun ω => w x + (J ω + B ω) + R ω) P :=
      ((integrable_const (w x)).add hJB).add hRi
    have hInt : (∫ ω, F n ω ∂P) ≤
        (∫ ω, w x + (J ω + B ω) + R ω ∂P) :=
      integral_mono_ae hF hComp hBound
    have hSum1 : (∫ ω, w x + (J ω + B ω) + R ω ∂P) =
        (∫ ω, w x + (J ω + B ω) ∂P) + (∫ ω, R ω ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add' ((integrable_const (w x)).add hJB) hRi)
    have hSum2 : (∫ ω, w x + (J ω + B ω) ∂P) =
        (∫ ω, w x ∂P) + (∫ ω, J ω + B ω ∂P) := by
      simpa only [Pi.add_apply] using
        (integral_add' (integrable_const (w x)) hJB)
    have hSum3 : (∫ ω, J ω + B ω ∂P) =
        (∫ ω, J ω ∂P) + (∫ ω, B ω ∂P) := by
      simpa only [Pi.add_apply] using (integral_add' hJi hBi)
    have hSplit : (∫ ω, w x + (J ω + B ω) + R ω ∂P) =
        w x + ((∫ ω, J ω ∂P) + (∫ ω, B ω ∂P)) +
          (∫ ω, R ω ∂P) := by
      rw [hSum1, hSum2, hSum3]
      simp
    rw [hSplit, hJ0] at hInt
    linarith
  have hMean : (∫ ω, F n ω ∂P) ≤ w x := by
    by_contra hbad
    have hε : 0 < ((∫ ω, F n ω ∂P) - w x) / 2 := by
      linarith
    have hb := hApprox _ hε
    linarith
  refine ⟨fun ω => F n ω - (∫ ξ, F n ξ ∂P),
    hF, hF.sub (integrable_const _), ?_, ?_⟩
  · have hZero : (∫ ω, F n ω - (∫ ξ, F n ξ ∂P) ∂P) = 0 := by
      change (∫ ω, ((F n) - fun _ : Ω => (∫ ξ, F n ξ ∂P)) ω ∂P) = 0
      rw [integral_sub' hF (integrable_const _)]
      simp
    exact le_of_eq hZero
  · exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)
