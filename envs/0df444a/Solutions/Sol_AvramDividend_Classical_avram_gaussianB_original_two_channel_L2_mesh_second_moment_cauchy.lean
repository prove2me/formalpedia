-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_two_channel_L2_mesh_second_moment_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:51:02.225394+00:00
-- url     : https://prove2.me/submissions/a6502f44-dab3-451e-bc75-d4d5ef5d4283

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_two_noise_physical_mesh_integral_square_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory AvramDividend.Classical
open scoped Topology
noncomputable section
/-- Full original Gaussian two-channel physical-grid second-moment Cauchy assembly. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (L Q : ℕ → Ω → ℝ)
    (hLInt : ∀ m l, Integrable (fun ω => (L m ω - L l ω) ^ 2) P)
    (hQInt : ∀ m, Integrable (fun ω => (Q m ω) ^ 2) P)
    (hMInt : ∀ m l, Integrable (fun ω =>
      ((L m ω + Q m ω) - (L l ω + Q l ω)) ^ 2) P)
    (hLCauchy : Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P)
        atTop (𝓝 (0 : ℝ)))
    (hQVanishing : Tendsto (fun m =>
      ∫ ω, (Q m ω) ^ 2 ∂P) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hQFirst :
      Tendsto (fun nm : ℕ × ℕ =>
        ∫ ω, (Q nm.1 ω) ^ 2 ∂P) atTop (𝓝 (0 : ℝ)) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hQVanishing.comp Filter.tendsto_fst
  have hQSecond :
      Tendsto (fun nm : ℕ × ℕ =>
        ∫ ω, (Q nm.2 ω) ^ 2 ∂P) atTop (𝓝 (0 : ℝ)) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hQVanishing.comp Filter.tendsto_snd
  have hRHS :
      Tendsto (fun nm : ℕ × ℕ =>
        2 * (∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P) +
        4 * (∫ ω, (Q nm.1 ω) ^ 2 ∂P) +
        4 * (∫ ω, (Q nm.2 ω) ^ 2 ∂P))
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_add, add_zero] using
      ((hLCauchy.const_mul 2).add (hQFirst.const_mul 4)).add
        (hQSecond.const_mul 4)
  have hUpper (nm : ℕ × ℕ) :
      (∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P) ≤
      2 * (∫ ω, (L nm.1 ω - L nm.2 ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q nm.1 ω) ^ 2 ∂P) +
      4 * (∫ ω, (Q nm.2 ω) ^ 2 ∂P) :=
    avram_gaussianB_two_noise_physical_mesh_integral_square_upper
      P L Q hLInt hQInt hMInt nm.1 nm.2
  have hLower (nm : ℕ × ℕ) :
      0 ≤ ∫ ω, ((L nm.1 ω + Q nm.1 ω) -
        (L nm.2 ω + Q nm.2 ω)) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  exact squeeze_zero hLower hUpper hRHS
