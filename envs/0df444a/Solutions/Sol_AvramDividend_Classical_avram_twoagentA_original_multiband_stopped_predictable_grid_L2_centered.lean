-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_multiband_stopped_predictable_grid_L2_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:48:35.480833+00:00
-- url     : https://prove2.me/submissions/5ae6fbf0-6c22-424c-9a13-bda2da8f2abd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ j, grid j ≤ grid (j + 1))
    (S : Finset ℕ) (a b : ℕ → ℕ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ i ∈ S, ∀ j,
      StronglyMeasurable[𝓕.rightCont (grid j)] (H i j))
    (K : ℕ → ℝ)
    (hBound : ∀ i ∈ S, ∀ j ω, |H i j ω| ≤ K i)
    (k : ℕ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((a i : ℝ) + 1))) (-(1 / ((b i : ℝ) + 1)))
    let N : ℕ → ℕ → Ω → ℝ≥0∞ := fun i j ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s,
          X.X s ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
        (Ioc (grid j) (grid (j + 1)) ×ˢ B i)
    let r : ℕ → ℕ → ℝ := fun i j =>
      (((grid (j + 1) - grid j : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
    let Z : ℕ → Ω → ℝ := fun i ω =>
      ∑ j ∈ Finset.range k,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid j : WithTop ℝ≥0)
          then (0 : ℝ) else H i j ω) * ((N i j ω).toReal - r i j)
    MemLp (fun ω => ∑ i ∈ S, Z i ω) 2 P ∧
      (∫ ω, ∑ i ∈ S, Z i ω ∂P) = 0 := by
  classical
  intro B N r Z
  have hOne (i : ℕ) (hi : i ∈ S) :
      MemLp (Z i) 2 P ∧ (∫ ω, Z i ω ∂P) = 0 := by
    simpa only [Z, N, r, B] using
      (avram_mix_annulus15_original_stopped_bounded_predictable_annulus_grid_L2_zero_mean
        X (a i) (b i) (hab i hi) τ hτstop grid hGrid
        (H i) (hH i hi) (K i) (hBound i hi) k)
  have hSum (F : Finset ℕ) (hF : F ⊆ S) :
      MemLp (fun ω => ∑ i ∈ F, Z i ω) 2 P ∧
        (∫ ω, ∑ i ∈ F, Z i ω ∂P) = 0 := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert i F hi ih =>
      have hiS : i ∈ S := hF (Finset.mem_insert_self i F)
      have hFS : F ⊆ S := Finset.Subset.trans (Finset.subset_insert i F) hF
      have hI := hOne i hiS
      have hR := ih hFS
      simp only [Finset.sum_insert hi]
      refine ⟨hI.1.add hR.1, ?_⟩
      have hIi : Integrable (Z i) P := hI.1.integrable (by norm_num)
      have hRi : Integrable (fun ω => ∑ j ∈ F, Z j ω) P :=
        hR.1.integrable (by norm_num)
      rw [integral_add hIi hRi, hI.2, hR.2]
      norm_num
  exact hSum S (Finset.Subset.rfl)
