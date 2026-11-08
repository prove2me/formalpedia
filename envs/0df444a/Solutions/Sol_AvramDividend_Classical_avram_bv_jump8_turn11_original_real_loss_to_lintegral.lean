-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn11_original_real_loss_to_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:15:17.198393+00:00
-- url     : https://prove2.me/submissions/8aa165e5-94af-4ac7-9711-3ef93fd7bf49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_original_shortcell_integrability
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_real_loss_pathwise_kernel

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The exact source pathwise finite-sum identity and actual marked-loss L1
establish the Bochner/ENNReal Campbell conversion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (∫ ω, L ω ∂P) =
      ((∫⁻ ω, ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
        (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P)).toReal := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
  let B : Set ℝ := Iio (-ε)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let K : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p in (Ioc 0 T ×ˢ (univ : Set ℝ)),
      (B.indicator φ) p.2 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hpath : ∀ ω : Ω, 0 ≤ L ω ∧ K ω = ENNReal.ofReal (L ω) := by
    simpa only [T, ε, φ, B, S, L, K] using
      (avram_bv_jump8_turn11_real_loss_pathwise_kernel X hX hBV k n)
  have hInt : Integrable L P := by
    have h := avram_bv_jump8_turn11_original_shortcell_integrability X hX hBV k n
    simpa only [T, S, W, L] using h.2
  have hnonneg : 0 ≤ᵐ[P] L :=
    Filter.Eventually.of_forall (fun ω => (hpath ω).1)
  have hreal : (∫ ω, L ω ∂P) =
      (∫⁻ ω, ENNReal.ofReal (L ω) ∂P).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnonneg hInt.aestronglyMeasurable
  have hker : (∫⁻ ω, ENNReal.ofReal (L ω) ∂P) =
      (∫⁻ ω, K ω ∂P) := by
    apply lintegral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => (hpath ω).2.symm)
  calc
    (∫ ω, L ω ∂P) = (∫⁻ ω, ENNReal.ofReal (L ω) ∂P).toReal := hreal
    _ = (∫⁻ ω, K ω ∂P).toReal := congrArg ENNReal.toReal hker
