-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB238_fixed_clipped_physical_mesh_two_level_null_occupation_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:50:28.137018+00:00
-- url     : https://prove2.me/submissions/dbe2259d-dc25-455c-9192-1e606e60a277

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB206_ae_clipped_mesh_L2_from_null_levels_and_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact fixed clipping levels: source path zero-occupation implies two-mesh L2 Cauchy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (Y : ℝ≥0 → Ω → ℝ)
    (hY : Measurable (fun z : ℝ≥0 × Ω => Y z.1 z.2))
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 |
        ¬ ContinuousAt (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (hn : 0 < n) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hρ : Measurable ρ)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (hDeriv : ∀ y ∈ Set.Ioo a b,
      ContinuousAt (deriv w) y)
    (hClosed : ContinuousOn (deriv w) (Set.Icc a b)) :
    let K : ℕ → ℝ → Ω → ℝ := fun m t ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      (Finset.range (m + 1)).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if (s : ℝ) ≤ t ∧ t < ((s + Δ : ℝ≥0) : ℝ)
        then if (s : ℝ) < (ρ ω : ℝ) then
          Real.exp (-(q * (s : ℝ))) *
            (if Y (Real.toNNReal (s : ℝ)) ω ∈ Set.Icc a b
              then deriv w (Y (Real.toNNReal (s : ℝ)) ω) else 1)
        else 0 else 0)
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ t in Set.Ioo (0 : ℝ) (n : ℝ),
        (∫ ω, (K mp.1 t ω - K mp.2 t ω)^2 ∂P) ∂volume)
      atTop (𝓝 (0 : ℝ)) := by
  intro K
  let H : ℝ → Ω → ℝ := fun t ω =>
    if t < (ρ ω : ℝ) then
      Real.exp (-(q * t)) *
        (if Y (Real.toNNReal t) ω ∈ Set.Icc a b
          then deriv w (Y (Real.toNNReal t) ω) else 1)
    else 0
  have hb :=
    avram_gbB215_generic_physical_clipped_mesh_measurable_bounded
      Y hY ρ hρ w a b hClosed q hq n hn
  have hAll :
      (∀ m, Measurable (fun z : ℝ × Ω => K m z.1 z.2)) ∧
      Measurable (fun z : ℝ × Ω => H z.1 z.2) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ m t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
          |K m t ω| ≤ B) ∧
        (∀ t ω, t ∈ Set.Ioo (0 : ℝ) (n : ℝ) →
          |H t ω| ≤ B) := by
    simpa only [K, H, Real.toNNReal_coe, NNReal.coe_lt_coe] using hb
  obtain ⟨hKm, hHm, B, hB, hKb, hHb⟩ := hAll
  have hlim :=
    avram_gbB206_ae_clipped_mesh_L2_from_null_levels_and_bounds
      P Y hCount n hn q w a b ρ hOccA hOccB hDeriv
      hKm hHm B B hB hB hKb hHb
  exact
    avram_gbB219_interval_bounded_one_mesh_L2_implies_two_mesh_cauchy
      P n hn K H hKm hHm B B hB hB hKb hHb hlim
