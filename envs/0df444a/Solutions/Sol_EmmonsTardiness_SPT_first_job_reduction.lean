-- Prove2me | solution 1 for EmmonsTardiness.SPT.first_job_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:35:53.61224+00:00
-- url     : https://prove2.me/submissions/6055cdb6-70e8-43af-9f2d-42c18330a52a

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_EmmonsTardiness_SPT_Model

set_option autoImplicit false

open MooreLateJobs in
theorem f311b3af_compl_cons_ne {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (k : ι) (l' : List ι)
    (i : ι) (hi : i ≠ k) :
    Shared.completionTime p (k :: l') i = p k + Shared.completionTime p l' i := by
  unfold Shared.completionTime Shared.completionAt
  rw [List.idxOf_cons_ne _ (Ne.symm hi)]
  simp [List.take_succ_cons]

open MooreLateJobs in
theorem f311b3af_compl_cons_self {ι : Type*} [DecidableEq ι] (p : ι → ℝ) (k : ι) (l' : List ι) :
    Shared.completionTime p (k :: l') k = p k := by
  unfold Shared.completionTime Shared.completionAt
  simp

open EmmonsTardiness.SPT MooreLateJobs in
theorem f311b3af_cons_shift {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (k : ι) (hk : k ∈ J) (l' : List ι) :
    totalTardiness p d J (k :: l') =
      max 0 (p k - d k) + totalTardiness p (fun i => d i - p k) (J.erase k) l' := by
  unfold totalTardiness
  rw [← Finset.add_sum_erase J _ hk]
  congr 1
  · simp [tardiness, f311b3af_compl_cons_self]
  · apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    simp only [tardiness, f311b3af_compl_cons_ne p k l' i hik]
    congr 1
    ring

open MooreLateJobs in
theorem f311b3af_tail_sched {ι : Type*} [DecidableEq ι] (J : Finset ι) (k : ι) (t : List ι)
    (h : Shared.IsSchedule J (k :: t)) : Shared.IsSchedule (J.erase k) t := by
  obtain ⟨hnd, hmem⟩ := h
  rw [List.nodup_cons] at hnd
  refine ⟨hnd.2, fun x => ?_⟩
  rw [Finset.mem_erase, ← hmem x, List.mem_cons]
  constructor
  · intro hx
    exact ⟨fun hxk => hnd.1 (hxk ▸ hx), Or.inr hx⟩
  · rintro ⟨hxk, hx | hx⟩
    · exact absurd hx hxk
    · exact hx

open MooreLateJobs in
theorem f311b3af_cons_sched {ι : Type*} [DecidableEq ι] (J : Finset ι) (k : ι) (hk : k ∈ J)
    (t : List ι) (h : Shared.IsSchedule (J.erase k) t) : Shared.IsSchedule J (k :: t) := by
  obtain ⟨hnd, hmem⟩ := h
  refine ⟨List.nodup_cons.2 ⟨fun hkt => ?_, hnd⟩, fun x => ?_⟩
  · have := (hmem k).1 hkt
    simp at this
  · rw [List.mem_cons, hmem x, Finset.mem_erase]
    constructor
    · rintro (rfl | ⟨_, hx⟩)
      · exact hk
      · exact hx
    · intro hx
      by_cases hxk : x = k
      · exact Or.inl hxk
      · exact Or.inr ⟨hxk, hx⟩

open EmmonsTardiness.SPT MooreLateJobs in
theorem solution {ι : Type*} [DecidableEq ι] (p d : ι → ℝ) (J : Finset ι)
    (k : ι) (hk : k ∈ J) (hfirst : ∃ l, IsOptimal p d J l ∧ l.head? = some k)
    (l' : List ι) (hl' : IsOptimal p (fun i => d i - p k) (J.erase k) l') :
    IsOptimal p d J (k :: l') := by
  obtain ⟨l, ⟨hls, hlopt⟩, hhead⟩ := hfirst
  obtain ⟨t, rfl⟩ : ∃ t, l = k :: t := by
    cases l with
    | nil => simp at hhead
    | cons a t =>
      simp at hhead
      exact ⟨t, by rw [hhead]⟩
  have ht := f311b3af_tail_sched J k t hls
  refine ⟨f311b3af_cons_sched J k hk l' hl'.1, fun m hm => ?_⟩
  have h1 := hl'.2 t ht
  have h2 := hlopt m hm
  rw [f311b3af_cons_shift p d J k hk] at h2 ⊢
  linarith
