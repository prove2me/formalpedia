-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_contact_fourth_integral_automatic_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:51:31.189093+00:00
-- url     : https://prove2.me/submissions/ee7a8f3a-8b10-41b3-923c-3befa0b9bb1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_L1_from_cell_fourth_moments
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
    (hσM : Measurable σ)
    (hVM : ∀ i ∈ S, Measurable (V i))
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P) :
    Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P ∧
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
      V i ω‖ ^ 4 ∂P) ≤
      ∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P := by
  classical
  let C : Ω → ℝ := fun ω =>
    ∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω
  have hCM : Measurable C := by
    have hSummand (i : ℕ) (hi : i ∈ S) :
        Measurable (fun ω => if a i < σ ω ∧ σ ω ≤ b i then V i ω else 0) := by
      have hs :
          MeasurableSet {ω : Ω | a i < σ ω ∧ σ ω ≤ b i} :=
        (measurableSet_lt (α := ℝ≥0) measurable_const hσM).inter
          (measurableSet_le (α := ℝ≥0) hσM measurable_const)
      exact Measurable.ite hs (hVM i hi) measurable_const
    have hSum : Measurable (fun ω =>
        ∑ i ∈ S, if a i < σ ω ∧ σ ω ≤ b i then V i ω else 0) :=
      Finset.measurable_sum S hSummand
    convert hSum using 1
    funext ω
    simp [C, Finset.sum_filter]
  let A : Ω → ℝ := fun ω => ‖C ω‖ ^ 4
  let B : Ω → ℝ := fun ω => ∑ i ∈ S, ‖V i ω‖ ^ 4
  have hAM : AEStronglyMeasurable A P :=
    (hCM.norm.pow_const 4).aestronglyMeasurable
  have hBI : Integrable B P :=
    integrable_finset_sum S (fun i hi => hVI i hi)
  have h0 : (fun _ : Ω => (0 : ℝ)) ≤ᵐ[P] A :=
    Filter.Eventually.of_forall (fun ω => pow_nonneg (norm_nonneg _) _)
  have hAB : A ≤ᵐ[P] B := by
    filter_upwards [] with ω
    exact avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
      S a b (σ ω) (fun i => V i ω) hSep
  have hAI : Integrable A P :=
    integrable_of_le_of_le hAM h0 hAB
      (integrable_zero Ω ℝ P) hBI
  have hTargetI : Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P :=
    hAI
  exact ⟨hTargetI,
    avram_b24_contact_fourth_L1_from_cell_fourth_moments
      S a b σ V hSep hVI hTargetI⟩
