-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB204_ae_clipped_uniform_mesh_tendsto_from_null_levels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:22:01.378175+00:00
-- url     : https://prove2.me/submissions/2a4b3aa1-83e8-4984-826e-add68c72bb07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB203_generic_good_mesh_times_from_two_null_levels
import Theorems.Thm_AvramDividend_Classical_avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pointwise physical-time convergence of clipped uniform step coefficients. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict
      (Ioo (0 : ℝ) (n : ℝ))),
      Tendsto (fun m : ℕ =>
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
          else 0)) atTop
        (𝓝 (if t < (ρ ω : ℝ) then
          Real.exp (-(q * t)) *
            (if Y (Real.toNNReal t) ω ∈ Icc a b
              then deriv w (Y (Real.toNNReal t) ω)
              else 1)
          else 0)) := by
  have hGood :=
    avram_gbB203_generic_good_mesh_times_from_two_null_levels
      Y hCount n a b ρ hOccA hOccB w hDeriv
  have hI : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      t ∈ Ioo (0 : ℝ) (n : ℝ) := by
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hGood] with ω hω
  filter_upwards [hω, hI] with t hgood ht
  rcases hgood with ⟨hY, ha, hb, hRho, hDerivAt⟩
  exact
    avram_gbB162_nnreal_step_clipped_pointwise_convergence_at_good_time
      n hn t ht q w a b
      (fun r : ℝ => Y (Real.toNNReal r) ω)
      hY hDerivAt ha hb (ρ ω : ℝ) hRho

