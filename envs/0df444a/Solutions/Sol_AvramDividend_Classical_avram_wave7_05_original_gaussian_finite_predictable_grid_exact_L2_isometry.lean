-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:01:58.959178+00:00
-- url     : https://prove2.me/submissions/b2bae8bb-b799-4655-a6cf-040dbe4baeb4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (s t : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (hLp : ∀ i ∈ S, MemLp (fun ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)) 2 P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (t i) ω - X.X (s i) ω -
      ((t i - s i) : ℝ) * X.c)
  change MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P)
  have hAll : ∀ i ∈ S, MemLp (F i) 2 P := by
    intro i hi
    exact hLp i hi
  have hSum : MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P :=
    memLp_finset_sum S hAll
  have hSquare : Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P :=
    hSum.integrable_sq
  have hDiagAll : ∀ i ∈ S,
      Integrable (fun ω => (F i ω) ^ 2) P := by
    intro i hi
    exact (hAll i hi).integrable_sq
  have hDiag : Integrable (fun ω => ∑ i ∈ S, (F i ω) ^ 2) P :=
    integrable_finset_sum S hDiagAll
  have hOff :=
    avram_wave7_05_original_gaussian_finite_offdiagonal_double_sum_mean_zero
      X hν S s t G hst hSep hGown hGpair hLp
  dsimp only at hOff
  have hAlg (ω : Ω) :
      (∑ i ∈ S, F i ω) ^ 2 =
        (∑ i ∈ S, (F i ω) ^ 2) +
          (∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω) := by
    calc
      (∑ i ∈ S, F i ω) ^ 2 =
          ∑ i ∈ S, F i ω * (∑ j ∈ S, F j ω) := by
            rw [sq, Finset.sum_mul]
      _ = ∑ i ∈ S, ∑ j ∈ S, F i ω * F j ω := by
          simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ S, ((F i ω) ^ 2 +
            (∑ j ∈ S.erase i, F i ω * F j ω)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hErase := Finset.sum_erase_add S
            (fun j => F i ω * F j ω) hi
          calc
            (∑ j ∈ S, F i ω * F j ω) =
                (∑ j ∈ S.erase i, F i ω * F j ω) +
                  F i ω * F i ω := hErase.symm
            _ = (F i ω) ^ 2 +
                (∑ j ∈ S.erase i, F i ω * F j ω) := by ring
      _ = (∑ i ∈ S, (F i ω) ^ 2) +
            (∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω) := by
          rw [Finset.sum_add_distrib]
  have hFunctions :
      (fun ω => (∑ i ∈ S, F i ω) ^ 2) =
        (fun ω => (∑ i ∈ S, (F i ω) ^ 2) +
          (∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω)) := by
    funext ω
    exact hAlg ω
  refine ⟨hSum, hSquare, ?_⟩
  calc
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
        ∫ ω, (∑ i ∈ S, (F i ω) ^ 2) +
          (∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω) ∂P := by
            rw [hFunctions]
    _ = (∫ ω, ∑ i ∈ S, (F i ω) ^ 2 ∂P) +
          (∫ ω, ∑ i ∈ S, ∑ j ∈ S.erase i, F i ω * F j ω ∂P) := by
            rw [integral_add hDiag hOff.1]
    _ = ∑ i ∈ S, ∫ ω, (F i ω) ^ 2 ∂P := by
          rw [integral_finset_sum S hDiagAll, hOff.2, add_zero]
