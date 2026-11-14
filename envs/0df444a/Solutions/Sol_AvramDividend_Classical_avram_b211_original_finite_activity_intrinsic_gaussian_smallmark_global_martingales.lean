-- Prove2me | solution 1 for AvramDividend.Classical.avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:07:03.60645+00:00
-- url     : https://prove2.me/submissions/feb753d7-cac2-45fd-8411-f585d481ba9f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Global original intrinsic Gaussian and compensated small-jump martingale sources need no jump-free interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
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
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) := by
  have hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      τ ω < u → u ≤ τ ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 :=
    Filter.Eventually.of_forall (fun ω u hlt hle =>
      (not_lt_of_ge hle hlt).elim)
  obtain ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hXsrc, _⟩ :=
    avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
      X hX hFinite n hn τ hτstop hτbound S hτrange
      τ τ (fun ω => le_rfl) hNoJump
  exact ⟨R, Jsmall, M, hRsrc, hJsrc, hRI, hJI, hRM, hJM, hXsrc⟩
