-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e2_original_source_signed_compensation_interior_cap_automatic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:47:12.95881+00:00
-- url     : https://prove2.me/submissions/b234577e-a4b6-4b30-884c-ef61db2e8d3c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
import Theorems.Thm_AvramDividend_Classical_avram_p3_e2_original_admissible_signed_source_budget_no_L1_assumption
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T) (hτ : IsStoppingTime 𝓕.rightCont
(fun ω => (τ ω : WithTop ℝ≥0))) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (w : ℝ → ℝ)
(hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
(ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b) (E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hBandWide : Icc (a / 2) b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
  X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
 :
  let Upre : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    Function.leftLim (fun v : ℝ≥0 =>
      x + X.X v p.2 - rightLimit D v p.2) p.1);
  let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := (fun p : (ℝ≥0 × Ω) × ℝ =>
    if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
       (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
    else 0);
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0;
  let F : ℝ≥0 × Ω → ℝ := (fun p : ℝ≥0 × Ω =>
    if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
      (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1) +
       (∫ z in Iio (0 : ℝ),
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1 + z) -
          w (Function.leftLim (fun v : ℝ≥0 =>
            x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
       q * w (Function.leftLim (fun v : ℝ≥0 =>
          x + X.X v p.2 - rightLimit D v p.2) p.1))
    else 0);
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict
{u : ℝ≥0 | 0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω -
Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)));
  let M : Ω → ℝ := fun ω => (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z)
∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  let B : Ω → ℝ := fun ω => (∫ t, F (t, ω) ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal));
  (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
  (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) := by
  have hEcap : ∀ p ∈ E, ENNReal.ofReal (Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) < C := by
    intro p hp
    have hy : Function.leftLim
        (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈
        Icc (a / 2) b := by
      rcases hEregion p hp with ⟨hl, hr⟩
      exact ⟨by linarith [ha], hr⟩
    exact (hBandWide hy).2
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen C
  obtain ⟨L, R, hL, hR, hLip, hWbound⟩ :=
    avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
      X hBV C w hw_cont hw_neg hw_smooth a b ha hab hOpen hBandWide
  have hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    apply hBandWide
    exact ⟨by have := hy.1; linarith [ha], hy.2⟩
  obtain ⟨A, hA, hDeriv⟩ :=
    avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
      X hBV C w hw_smooth a b hab hBand
  exact avram_p3_e2_original_admissible_signed_source_budget_no_L1_assumption
    X hBV T τ hτBound hτ x C D hD w hw_cont hw_neg q hq
    a b L R A ha ha2 hab hL hR hA hLip hWbound
    E hEm hEregion hDeriv hw_gen hEcap
