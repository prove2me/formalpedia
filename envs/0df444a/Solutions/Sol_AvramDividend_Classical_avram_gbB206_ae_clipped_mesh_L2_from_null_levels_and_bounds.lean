-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB206_ae_clipped_mesh_L2_from_null_levels_and_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:28:49.975098+00:00
-- url     : https://prove2.me/submissions/60e228d8-7c55-45c0-abbc-d034891d0e95

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
import Theorems.Thm_AvramDividend_Classical_avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Dominated time-and-probability L2 from almost-everywhere exact mesh convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℝ≥0 → Ω → ℝ)
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 | ¬ ContinuousAt
        (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (hn : 0 < n) (q : ℝ) (w : ℝ → ℝ)
    (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (hDeriv : ∀ y ∈ Ioo a b, ContinuousAt (deriv w) y) :
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ) then
          if (s : ℝ) < (ρ ω : ℝ) then
            Real.exp (-(q * (s : ℝ))) *
              (if Y (Real.toNNReal (s : ℝ)) ω ∈ Icc a b
                then deriv w (Y (Real.toNNReal (s : ℝ)) ω)
                else 1)
          else 0
        else 0)
    let H : ℝ → Ω → ℝ := fun t ω =>
      if t < (ρ ω : ℝ) then
        Real.exp (-(q * t)) *
          (if Y (Real.toNNReal t) ω ∈ Icc a b
            then deriv w (Y (Real.toNNReal t) ω)
            else 1)
      else 0
    (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) →
    Measurable (fun z : ℝ × Ω => H z.1 z.2) →
    ∀ (BK BH : ℝ), 0 ≤ BK → 0 ≤ BH →
      (∀ m t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) →
        |K m t ω| ≤ BK) →
      (∀ t ω, t ∈ Ioo (0 : ℝ) (n : ℝ) →
        |H t ω| ≤ BH) →
      Tendsto (fun m : ℕ =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          (∫ ω, (K m t ω - H t ω) ^ 2 ∂P) ∂volume)
        atTop (𝓝 (0 : ℝ)) := by
  intro K H hKm hHm BK BH hBK hBH hKb hHb
  have hae :=
    avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
      (P := P) Y hCount n hn q w a b ρ hOccA hOccB hDeriv
  exact avram_gbB157_ae_L2_on_time_interval_from_bounded_double_ae
    P n hn K H hKm hHm BK BH hBK hBH hKb hHb
    (by simpa only [K, H] using hae)

