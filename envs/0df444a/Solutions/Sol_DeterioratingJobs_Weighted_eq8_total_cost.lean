-- Prove2me | solution 1 for DeterioratingJobs.Weighted.eq8_total_cost
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T10:00:07.299372+00:00
-- url     : https://prove2.me/submissions/c9311858-0e6f-444d-9c23-962e627e8c6c

import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model



namespace DeterioratingJobs.Weighted

open MeasureTheory

theorem eq2_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (k : ℕ) (hk : k ≤ N) (ω : Ω) :
    DeterioratingJobs.Makespan.completionTime X α π k ω =
      ∑ i : Fin N with i.val < k,
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r)) := by
  induction k with
  | zero => simp [DeterioratingJobs.Makespan.completionTime]
  | succ k ih =>
    have hkN : k < N := hk
    have ih' := ih hkN.le
    have hstep : DeterioratingJobs.Makespan.completionTime X α π (k+1) ω =
        DeterioratingJobs.Makespan.completionTime X α π k ω +
          DeterioratingJobs.Makespan.actualProcessingTime X α (π ⟨k, hkN⟩)
            (DeterioratingJobs.Makespan.completionTime X α π k ω) ω := by
      simp [DeterioratingJobs.Makespan.completionTime, hkN]
    rw [hstep, ih']
    unfold DeterioratingJobs.Makespan.actualProcessingTime
    have hs : (Finset.univ.filter (fun i : Fin N => i.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]; omega
    rw [hs, Finset.sum_insert (by simp)]
    have hp : ∀ i : Fin N, i.val < k →
        (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k+1)) =
        insert ⟨k, hkN⟩ (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k)) := by
      intro i hi
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.lt_def]; omega
    have hp0 : (Finset.univ.filter (fun r : Fin N => (⟨k, hkN⟩ : Fin N) < r ∧ r.val < k+1)) = ∅ := by
      ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, Fin.lt_def]; omega
    rw [hp0, Finset.prod_empty, mul_one]
    have : ∀ i ∈ Finset.univ.filter (fun i : Fin N => i.val < k),
        X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k+1, (1 + α (π r)) =
        (X (π i) ω * ∏ r : Fin N with i < r ∧ r.val < k, (1 + α (π r))) * (1 + α (π ⟨k, hkN⟩)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hp i hi, Finset.prod_insert (by simp)]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    ring

theorem eq8_core {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) :
    totalCost X α c π ω =
      ∑ k : Fin N, c (π k) *
        ∑ i : Fin N with i ≤ k,
          X (π i) ω * ∏ r : Fin N with i < r ∧ r ≤ k, (1 + α (π r)) := by
  unfold totalCost
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eq2_core X α π (k.val+1) k.isLt ω]
  have h1 : (Finset.univ.filter (fun i : Fin N => i.val < k.val + 1)) =
      Finset.univ.filter (fun i : Fin N => i ≤ k) := by
    apply Finset.filter_congr; intro i _; rw [Fin.le_def]; omega
  have h2 : ∀ i : Fin N, (Finset.univ.filter (fun r : Fin N => i < r ∧ r.val < k.val + 1)) =
      Finset.univ.filter (fun r : Fin N => i < r ∧ r ≤ k) := by
    intro i
    apply Finset.filter_congr; intro r _; rw [Fin.le_def]; omega
  rw [h1]
  simp only [h2]

end DeterioratingJobs.Weighted

open DeterioratingJobs.Weighted


theorem solution {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (ω : Ω) :
    totalCost X α c π ω =
      ∑ k : Fin N, c (π k) *
        ∑ i : Fin N with i ≤ k,
          X (π i) ω * ∏ r : Fin N with i < r ∧ r ≤ k, (1 + α (π r)) := by
  exact eq8_core X α c π ω
