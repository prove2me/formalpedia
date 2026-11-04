-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_eventual_finite_envelope_strong_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:53:05.020623+00:00
-- url     : https://prove2.me/submissions/32976b7c-3a19-4dcd-bf36-f24ef6b552fb

import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_squared_enorm_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_eventual_l2_strong_L1_convergence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! A finite eventual ENNReal squared envelope gives strong real L¹ convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (G : ℕ → Ω → ENNReal)
    (K : ENNReal) (N : ℕ) (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hdom : ∀ n, ∀ᵐ ω ∂P, ‖Y n ω‖ₑ ≤ G n ω)
    (hB : ∀ n, N ≤ n → (∫⁻ ω, (G n ω) ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by
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
  exact avram_p2_j_ui_eventual_l2_strong_L1_convergence
    P Y Z B N hm hLp hae
