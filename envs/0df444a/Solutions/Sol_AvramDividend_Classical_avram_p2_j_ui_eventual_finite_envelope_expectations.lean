-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:42:40.423648+00:00
-- url     : https://prove2.me/submissions/33df5be6-1a94-44e2-bf30-3307be26d4bf

import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_ae_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Arbitrary finite eventual ENNReal grid-envelope constants give real mean convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (K : ENNReal) (N : ℕ) (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n → (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  let B : ℝ≥0 := NNReal.sqrt K.toNNReal
  have hKsq : K = (B : ENNReal) ^ 2 := by
    calc
      K = (K.toNNReal : ENNReal) := (ENNReal.coe_toNNReal hK).symm
      _ = (((NNReal.sqrt K.toNNReal) ^ 2 : ℝ≥0) : ENNReal) := by
        exact congrArg (fun x : ℝ≥0 => (x : ENNReal))
          (NNReal.sq_sqrt K.toNNReal).symm
      _ = (B : ENNReal) ^ 2 := by
        rw [← ENNReal.coe_pow]
  have hLp : ∀ n, N ≤ n → eLpNorm (Y n) 2 P ≤ (B : ENNReal) := by
    intro n hn
    apply avram_p2_j_ui_lintegral_squared_enorm_bound P (Y n) B
    have hpow : ∀ᵐ ω ∂P,
        ‖Y n ω‖ₑ ^ (2 : ℝ) ≤ (G n ω) ^ (2 : ℝ) := by
      filter_upwards [hdom n] with ω hω
      gcongr <;> exact hω
    calc
      (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤
          (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) := lintegral_mono_ae hpow
      _ ≤ K := hB n hn
      _ = (B : ENNReal) ^ 2 := hKsq
  exact avram_p2_j_ui_eventual_l2_ae_expectations
    P Y Z B N hm hLp hae
