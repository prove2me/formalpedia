-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_terminal_gaussian_contact_L4_meshrate_from_original_cell_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:47:08.56427+00:00
-- url     : https://prove2.me/submissions/8e961486-dedf-47c7-b19c-98d0c6a0ece4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_L1_from_cell_fourth_moments
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (h : ℕ → ℝ≥0)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P)
    (hContactI : Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P)
    (hFourth : ∀ i ∈ S,
      (∫ ω, ‖V i ω‖ ^ 4 ∂P) ≤ 2 * X.σ ^ 4 * (h i : ℝ) ^ 2)
    (ε T : ℝ) (hε : 0 ≤ ε)
    (hmax : ∀ i ∈ S, (h i : ℝ) ≤ ε)
    (hT : (∑ i ∈ S, (h i : ℝ)) ≤ T) :
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
      V i ω‖ ^ 4 ∂P) ≤ 2 * X.σ ^ 4 * ε * T := by
  have hContact :=
    avram_b24_contact_fourth_L1_from_cell_fourth_moments
      S a b σ V hSep hVI hContactI
  have hCells :
      (∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P) ≤
      (∑ i ∈ S, 2 * X.σ ^ 4 * (h i : ℝ) ^ 2) :=
    Finset.sum_le_sum (fun i hi => hFourth i hi)
  have hFactor :
      (∑ i ∈ S, 2 * X.σ ^ 4 * (h i : ℝ) ^ 2) =
      2 * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) := by
    simp only [Finset.mul_sum, mul_assoc]
  have hMesh :=
    (avram_p4_a_gaussian_original_sigma_fourth_moment_mesh_error_bound
      X S h T ε hε hmax hT).2
  calc
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
      V i ω‖ ^ 4 ∂P) ≤
        ∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P := hContact
    _ ≤ ∑ i ∈ S, 2 * X.σ ^ 4 * (h i : ℝ) ^ 2 := hCells
    _ = 2 * X.σ ^ 4 * (∑ i ∈ S, (h i : ℝ) ^ 2) := hFactor
    _ ≤ 2 * X.σ ^ 4 * ε * T := hMesh
