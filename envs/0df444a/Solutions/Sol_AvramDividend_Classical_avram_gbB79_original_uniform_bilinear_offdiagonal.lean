-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB79_original_uniform_bilinear_offdiagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:27:05.216168+00:00
-- url     : https://prove2.me/submissions/0ec386ca-435d-46c6-90dd-dfcac1d1a312

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB81_original_mixed_cells_zero
import Theorems.Thm_AvramDividend_Classical_avram_gbB82_finite_L2_bilinear_diag
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N)
    (H J : ℕ → Ω → ℝ)
    (hHAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (H i))
    (hJAdapt : ∀ (i : ℕ), Measurable[𝓕.rightCont ((i : ℝ≥0) * ((n : ℝ≥0) / (N : ℝ≥0)))] (J i))
    (hHBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |H i ω| ≤ B)
    (hJBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ω, |J i ω| ≤ B) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∫ ω, ((Finset.range N).sum (fun i => H i ω * Z i ω)) *
        ((Finset.range N).sum (fun i => J i ω * Z i ω)) ∂P) =
      (Finset.range N).sum (fun i => ∫ ω, (H i ω * Z i ω) * (J i ω * Z i ω) ∂P) := by
  intro Δ s Z
  have hLp (W : ℕ → Ω → ℝ)
      (hAdapt : ∀ k, Measurable[𝓕.rightCont (s k)] (W k))
      (hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ k ω, |W k ω| ≤ C)
      (k : ℕ) : MemLp (fun ω => W k ω * Z k ω) 2 P := by
    obtain ⟨C, hC, hCbd⟩ := hBound
    have hGlobal : Measurable (W k) :=
      (hAdapt k).mono (𝓕.rightCont.le _) le_rfl
    have hStop : IsStoppingTime 𝓕.rightCont
        (fun ω : Ω => ((s k : ℝ≥0) : WithTop ℝ≥0)) :=
      isStoppingTime_const 𝓕.rightCont (s k)
    have hh := avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (fun _ : Ω => s k) hStop (s k)
      (by intro ω; exact le_refl _) Δ (W k) hGlobal.stronglyMeasurable
      C hC (hCbd k)
    simpa only [Z, NNReal.coe_add, add_sub_cancel_left] using hh
  have hAdaptH : ∀ k, Measurable[𝓕.rightCont (s k)] (H k) := by
    intro k
    simpa only [s, Δ] using hHAdapt k
  have hAdaptJ : ∀ k, Measurable[𝓕.rightCont (s k)] (J k) := by
    intro k
    simpa only [s, Δ] using hJAdapt k
  have hCross : ∀ i j, i ≠ j →
      (∫ ω, (H i ω * Z i ω) * (J j ω * Z j ω) ∂P) = 0 := by
    simpa only [Z, s, Δ] using
      (avram_gbB81_original_mixed_cells_zero
        X hν n N hn hN H J hHAdapt hJAdapt hHBound hJBound)
  exact avram_gbB82_finite_L2_bilinear_diag P N
    (fun i ω => H i ω * Z i ω) (fun i ω => J i ω * Z i ω)
    (hLp H hAdaptH hHBound)
    (hLp J hAdaptJ hJBound) hCross
