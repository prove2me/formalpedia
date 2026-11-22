-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_finite_activity_expected_positive_clock_reward_budget_case_nonzeroNu_finitecap
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:51:12.024827+00:00
-- url     : https://prove2.me/submissions/36187476-2b3c-4776-b594-bf6d1b8caffc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261122_restricted_negative_mark_proved_sources_for_original
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_mark_generator_strict_negative_mass
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxpos : 0 < x)
    (k : ℕ) (hk : 0 < k)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (k : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in
      paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hCashI : Integrable Cash P)
    (hNuNonzero : X.ν ≠ 0) (hFiniteCap : C ≠ ⊤) :
    MeasurableSet {ω : Ω | τ ω ≠ 0} ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    (∫ ω in {η : Ω | τ η ≠ 0}, Term ω + Cash ω ∂P) ≤
      w x * (P {η : Ω | τ η ≠ 0}).toReal := by
  apply AvramDividend.Classical.avram_bridge20261122_restricted_negative_mark_proved_sources_for_original X hX hBV hFinite q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_hjb x hx hxc D hD hxpos k hk τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm hCashI hNuNonzero hFiniteCap
  exact ⟨AvramDividend.Classical.avram_jump6_A_discounted_genuine_negative_mark_mesh_generator_nonpositive X,
    AvramDividend.Classical.avram_jump6_A_true_overshooting_negative_Levy_mesh_compensator_exact X,
    AvramDividend.Classical.avram_jump6_A_large_negative_mark_generator_strict_negative_mass X⟩
