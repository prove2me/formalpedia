-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_finiteactivity_true_stopped_marked_mesh_smallmodulus_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:37:51.461361+00:00
-- url     : https://prove2.me/submissions/a0927e26-d188-49ea-8686-2d7399b5e05e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
import Theorems.Thm_AvramDividend_Classical_avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (marked : ℕ → Ω → Finset ℕ)
    (hmarked : ∀ m ω, marked m ω =
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let grid : ℕ → ℝ≥0 := fun i =>
        min ((i : ℝ≥0) * Δ) (σ ω)
      (by
        classical
        exact (Finset.range (m + 1)).filter (fun i =>
          ∃ u : ℝ≥0, grid i < u ∧ u ≤ grid (i + 1) ∧
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)))
    (W : ℕ → Ω → ℕ → ℝ)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P)
    (ε : ℕ → ℝ)
    (hεnonneg : ∀ m, 0 ≤ ε m)
    (hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hW : ∀ m, ∀ᵐ ω ∂P, ∀ i ∈ marked m ω,
      ‖W m ω i‖ ≤ ε m) :
    (∀ m, Integrable
      (fun ω => ∑ i ∈ marked m ω, W m ω i) P) ∧
    Tendsto
      (fun m => ∫ ω, ‖∑ i ∈ marked m ω, W m ω i‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {t : ℝ≥0 |
      0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
      (fun t : ℝ≥0 => (t,
        X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
  let N : Ω → ℝ := fun ω =>
    ((NX ω) (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal
  have hNI : Integrable N P := by
    simpa only [NX, N] using
      avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
        X hFinite n
  have hDom : ∀ m, ∀ᵐ ω ∂P,
      ((marked m ω).card : ℝ) ≤ N ω := by
    intro m
    have hm :=
      avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
        X hFinite n m σ hσstop hσbound
    rcases hm with ⟨_, _, hBound⟩
    filter_upwards [hBound] with ω hb
    simpa only [hmarked m ω, NX, N] using hb
  exact avram_b253_original_marked_physical_source_smallmodulus_Poisson_dom_L1_vanish
    marked N hNI hDom W hMeas ε hεnonneg hεzero hW
