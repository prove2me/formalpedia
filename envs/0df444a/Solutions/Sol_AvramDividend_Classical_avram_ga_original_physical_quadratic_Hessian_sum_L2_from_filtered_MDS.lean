-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_physical_quadratic_Hessian_sum_L2_from_filtered_MDS
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T07:57:30.391252+00:00
-- url     : https://prove2.me/submissions/7c117c72-6ade-40d7-8b34-efdf19d00d62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
import Theorems.Thm_AvramDividend_Classical_avram_ga_rightCont_physical_time_MDS_to_natural_grid_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H U : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ (m i : ℕ), i < m + 1 →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2)) ^ 2) P)
    (hUeq : ∀ (m i : ℕ) (ω : Ω),
      U m i ω =
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 - (Δ : ℝ) * X.σ ^ 2))
    (hULp : ∀ m i, MemLp (U m i) 2 P)
    (hUadapt : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      StronglyMeasurable[𝓕.rightCont (((i + 1 : ℕ) : ℝ≥0) * Δ)] (U m i))
    (hUcenter : ∀ (m i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      P[U m i | 𝓕.rightCont ((i : ℝ≥0) * Δ)] =ᵐ[P]
        (fun _ => (0 : ℝ))) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ m : ℕ,
      (∫ ω, (∑ i ∈ Finset.range (m + 1), U m i ω) ^ 2 ∂P) ≤
        J / ((m : ℝ) + 1) := by
  obtain ⟨J, hJ, hCell⟩ :=
    avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
      X hX hν n hn H K hK hH (by
        intro m i hi
        exact hHI m i (Finset.mem_range.mp hi))
  refine ⟨J, hJ, ?_⟩
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hs : Monotone s := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (show (0 : ℝ≥0) ≤ Δ from zero_le)
  obtain ⟨𝓖, h𝓖, hA, hC⟩ :=
    avram_ga_rightCont_physical_time_MDS_to_natural_grid_filtration
      P 𝓕 s hs (U m)
      (by simpa [s, Δ] using hUadapt m)
      (by simpa [s, Δ] using hUcenter m)
  have hVar : ∀ i < m + 1,
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        J * (1 / ((m : ℝ) + 1)) ^ 2 := by
    intro i hi
    have hc := hCell m i (Finset.mem_range.mpr hi)
    have hc' : (∫ ω, (U m i ω) ^ 2 ∂P) ≤
        J / (((m + 1 : ℕ) : ℝ) ^ 2) := by
      simpa only [hUeq] using hc
    calc
      (∫ ω, (U m i ω) ^ 2 ∂P) ≤
          J / (((m + 1 : ℕ) : ℝ) ^ 2) := hc'
      _ = J * (1 / ((m : ℝ) + 1)) ^ 2 := by
        simp [Nat.cast_add, Nat.cast_one, add_comm, div_eq_mul_inv, inv_pow] <;> ring
  have hB := avram_ga_predictable_centered_quadratic_mesh_L2_diagonal_bound
    P 𝓖 (U m) (hULp m) hA hC (m + 1) J
    (1 / ((m : ℝ) + 1)) hVar
  calc
    (∫ ω, (∑ i ∈ Finset.range (m + 1), U m i ω) ^ 2 ∂P) ≤
        ((m + 1 : ℕ) : ℝ) * (J * (1 / ((m : ℝ) + 1)) ^ 2) := hB
    _ = J / ((m : ℝ) + 1) := by
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp <;> ring
