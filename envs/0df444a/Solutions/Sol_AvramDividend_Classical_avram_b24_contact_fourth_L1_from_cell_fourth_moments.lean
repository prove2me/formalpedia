-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_contact_fourth_L1_from_cell_fourth_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:41:44.669508+00:00
-- url     : https://prove2.me/submissions/7d093e31-6d23-496c-b556-46d578ba21cd

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P)
    (hContactI : Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P) :
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
        V i ω‖ ^ 4 ∂P) ≤
      ∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P := by
  classical
  let A : Ω → ℝ := fun ω =>
    ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4
  let B : Ω → ℝ := fun ω => ∑ i ∈ S, ‖V i ω‖ ^ 4
  have hBI : Integrable B P := by
    exact integrable_finset_sum S (fun i hi => hVI i hi)
  have hBound : A ≤ᵐ[P] B := by
    filter_upwards [] with ω
    exact avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
      S a b (σ ω) (fun i => V i ω) hSep
  have hInt : (∫ ω, A ω ∂P) ≤ (∫ ω, B ω ∂P) :=
    integral_mono_ae hContactI hBI hBound
  change (∫ ω, A ω ∂P) ≤
    (∫ ω, ∑ i ∈ S, ‖V i ω‖ ^ 4 ∂P) at hInt
  rw [integral_finset_sum S (fun i hi => hVI i hi)] at hInt
  exact hInt
