-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_eventually_exact_grid_fatou_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:47:46.013755+00:00
-- url     : https://prove2.me/submissions/5d984d9b-22f7-4d45-8a49-7ddcab206a05

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞) (r : ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hBound : ∀ n ω, F n ω ≤ K ω)
    (hEventually : ∀ ω, ∀ᶠ n in atTop, F n ω = K ω)
    (hRate : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 r)) :
    (∫⁻ ω, K ω ∂P) = r := by
  have hLim : ∀ ω, Tendsto (fun n => F n ω) atTop (𝓝 (K ω)) := by
    intro ω
    have hEq : (fun n : ℕ => F n ω) =ᶠ[atTop] (fun _ => K ω) := hEventually ω
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => K ω) atTop (𝓝 (K ω))).congr' hEq.symm
  have hFatou : (∫⁻ ω, K ω ∂P) ≤ r := by
    calc
      (∫⁻ ω, K ω ∂P) =
          ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
            congr 1
            funext ω
            exact (hLim ω).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂P) atTop :=
        MeasureTheory.lintegral_liminf_le hFm
      _ = r := hRate.liminf_eq
  have hReverse : r ≤ ∫⁻ ω, K ω ∂P :=
    le_of_tendsto hRate (Filter.Eventually.of_forall fun n =>
      lintegral_mono (hBound n))
  exact le_antisymm hFatou hReverse