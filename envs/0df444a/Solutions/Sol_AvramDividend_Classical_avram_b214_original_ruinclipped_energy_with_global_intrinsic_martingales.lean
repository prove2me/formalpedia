-- Prove2me | solution 1 for AvramDividend.Classical.avram_b214_original_ruinclipped_energy_with_global_intrinsic_martingales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:55:48.040064+00:00
-- url     : https://prove2.me/submissions/ed6dff9a-ad4f-475d-a955-932ba4ac0e2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
import Theorems.Thm_AvramDividend_Classical_avram_b210_original_canonical_ruinclipped_mixed_energy_from_intrinsic_gaussian_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact original intrinsic noise martingales and stopped mixed energy, conditional only on residual grid L2. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (J : Ω → Finset ℕ)
    (grid : Ω → ℕ → ℝ≥0)
    (hGridMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hGridBound : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ (n : ℝ≥0))
    (hGridEndpoints : ∀ ω i, i ∈ S →
      s i ω = grid ω i ∧ t i ω = grid ω (i + 1))
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
 :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (Integrable (fun ω => ∑ i ∈ S, (R (t i ω) ω - R (s i ω) ω)^2) P →
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (R (t i ω) ω - R (s i ω) ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))^2 * (∫ ω, D ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 * (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) := by
  classical
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun _ : Ω => (0 : WithTop ℝ≥0)) := by
    simpa using
      (MeasureTheory.isStoppingTime_const 𝓕.rightCont (0 : ℝ≥0))
  obtain ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hXsrc⟩ :=
    avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
      X hX hFinite 1 (by decide) (fun _ : Ω => 0) hStop
      (by intro ω; simp) ({0} : Finset ℝ≥0)
      (by intro ω; simp)
  refine ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hXsrc, ?_⟩
  intro hGI
  exact avram_b210_original_canonical_ruinclipped_mixed_energy_from_intrinsic_gaussian_source
    X hFinite x hx C D hD n ρ hρbound hρclip κ hκexact
    k S s t (fun i ω => R (t i ω) ω - R (s i ω) ω)
    J (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) R Jsmall
    grid hGridMono hGridMeas hGridBound hGridEndpoints hJcanon
    hRsrc hJsrc (by intro ω i hi; rfl) rfl
    hInterior hsStop htStop hGI
