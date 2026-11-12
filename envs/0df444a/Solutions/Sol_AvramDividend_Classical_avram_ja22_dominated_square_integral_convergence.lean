-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja22_dominated_square_integral_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:19:51.612886+00:00
-- url     : https://prove2.me/submissions/89bc29b4-4629-419f-b4da-13b40a07b02e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hf : ∀ k : ℕ, AEStronglyMeasurable (f k) P)
    (hlim : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => f k ω) atTop (nhds (g ω)))
    (hB : Integrable (fun ω => (B ω) ^ 2) P)
    (hdom : ∀ᵐ ω ∂P, ∀ k : ℕ, ‖f k ω‖ ≤ B ω) :
    Tendsto (fun k : ℕ => ∫ ω, (f k ω) ^ 2 ∂P)
      atTop (nhds (∫ ω, (g ω) ^ 2 ∂P)) := by
  have hMeas : ∀ k : ℕ,
      AEStronglyMeasurable (fun ω => (f k ω) ^ 2) P := by
    intro k
    exact (hf k).pow 2
  have hBound : ∀ k : ℕ,
      ∀ᵐ ω ∂P, ‖(f k ω) ^ 2‖ ≤ (B ω) ^ 2 := by
    intro k
    filter_upwards [hdom] with ω hd
    have hb : 0 ≤ B ω :=
      le_trans (norm_nonneg (f k ω)) (hd k)
    calc
      ‖(f k ω) ^ 2‖ = ‖f k ω‖ ^ 2 := norm_pow (f k ω) 2
      _ ≤ (B ω) ^ 2 := by
        nlinarith [mul_nonneg
          (sub_nonneg.mpr (hd k))
          (add_nonneg hb (norm_nonneg (f k ω)))]
  have hLimSq : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => (f k ω) ^ 2) atTop (nhds ((g ω) ^ 2)) := by
    filter_upwards [hlim] with ω hw
    exact hw.pow 2
  exact tendsto_integral_of_dominated_convergence
    (fun ω => (B ω) ^ 2) hMeas hB hBound hLimSq
