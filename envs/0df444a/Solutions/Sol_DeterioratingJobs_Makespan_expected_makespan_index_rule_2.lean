-- Prove2me | solution 2 for DeterioratingJobs.Makespan.expected_makespan_index_rule
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:42.603423+00:00
-- url     : https://prove2.me/submissions/6ed0fe47-681a-42dc-a8de-ce39bd662906

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum
import Definitions.Def_DeterioratingJobs_Makespan_Model
import Theorems.Thm_DeterioratingJobs_Makespan_eq2_completion_closed_form
import Theorems.Thm_DeterioratingJobs_Makespan_lemma1_interchange

-- carved verbatim out of submission 6e52c998-f8ae-483a-85d3-6484c718d8d4, lines 204-210

section
open DeterioratingJobs
open DeterioratingJobs.Makespan
open MeasureTheory

theorem expmk_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    expectedMakespan P X α π =
      lemma1Sum (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) π := by
  unfold expectedMakespan lemma1Sum makespan
  have h : ∀ ω, completionTime X α π N ω = ∑ i : Fin N, X (π i) ω * ∏ r ∈ Finset.Ioi i, (1 + α (π r)) := by
    intro ω
    rw [DeterioratingJobs.Makespan.eq2_completion_closed_form X α π N le_rfl ω]
    have hu : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ := by ext; simp
    rw [hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext r; simp
  simp_rw [h]
  rw [integral_finsetSum _ (fun i _ => (hX (π i)).mul_const _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const]

theorem index_rule_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (hα : ∀ i, 0 < α i) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (fun k : Fin N => (∫ ω, X (π k) ω ∂P) / α (π k))) :
    ∀ σ : Equiv.Perm (Fin N), expectedMakespan P X α π ≤ expectedMakespan P X α σ := by
  intro σ
  rw [expmk_core P X hX α π, expmk_core P X hX α σ]
  refine (DeterioratingJobs.Makespan.lemma1_interchange (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) (fun i => by linarith [hα i]) π).1 ?_ σ
  simpa using hπ

end

section
open DeterioratingJobs.Makespan
open MeasureTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (hα : ∀ i, 0 < α i) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (fun k : Fin N => (∫ ω, X (π k) ω ∂P) / α (π k))) :
    ∀ σ : Equiv.Perm (Fin N), expectedMakespan P X α π ≤ expectedMakespan P X α σ := by
  exact index_rule_core P X hX α hα π hπ

end
