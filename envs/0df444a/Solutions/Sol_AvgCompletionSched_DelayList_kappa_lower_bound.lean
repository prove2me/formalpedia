-- Prove2me | solution 1 for AvgCompletionSched.DelayList.kappa_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T06:02:58.550992+00:00
-- url     : https://prove2.me/submissions/d1ca3831-a049-4b47-be97-bda83846420a

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model

open AvgCompletionSched.DelayList

variable {n : ℕ}

private theorem kappa_eq (I : Instance n) (j : Fin n) :
    kappa I j = if h : (I.preds j).Nonempty then
      I.p j + max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun i => kappa I i.1)) (I.r j)
    else I.p j + I.r j := by
  unfold kappa
  rw [WellFounded.fix_eq]

private theorem mem_preds (I : Instance n) {i j : Fin n} : i ∈ I.preds j ↔ I.prec i j := by
  simp only [Instance.preds, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem pr_le_kappa (I : Instance n) (j : Fin n) : I.p j + I.r j ≤ kappa I j := by
  rw [kappa_eq I j]
  split_ifs with h
  · have := le_max_right ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
      (fun i => kappa I i.1)) (I.r j)
    linarith
  · exact le_refl _

private theorem kappa_prec (I : Instance n) (i j : Fin n) (hij : I.prec i j) :
    I.p j + kappa I i ≤ kappa I j := by
  have hmem : i ∈ I.preds j := (mem_preds I).mpr hij
  rw [kappa_eq I j]
  split_ifs with h2
  · have h1 : kappa I i ≤ (I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h2)
        (fun x => kappa I x.1) :=
      Finset.le_sup' (fun x : {x // x ∈ I.preds j} => kappa I x.1)
        (Finset.mem_attach _ ⟨i, hmem⟩)
    have h3 := le_max_left ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h2)
      (fun x => kappa I x.1)) (I.r j)
    linarith
  · exact absurd (⟨i, hmem⟩ : (I.preds j).Nonempty) h2

private theorem kappa_le_C (I : Instance n) (m : ℕ) (N : Schedule I m) (j : Fin n) :
    kappa I j ≤ N.C j := by
  refine I.prec_wf.fix (C := fun x => kappa I x ≤ N.C x) ?_ j
  intro j ih
  have hSj : ∀ i, I.prec i j → kappa I i ≤ N.S j := by
    intro i hij
    have h1 := ih i hij
    have h2 := N.precedence i j hij
    rw [Schedule.C] at h1
    have h3 : 0 < I.p i := I.p_pos i
    linarith
  rw [kappa_eq I j, Schedule.C]
  split_ifs with h
  · have hsup : (I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun x => kappa I x.1) ≤ N.S j := by
      refine Finset.sup'_le _ _ ?_
      intro x _
      exact hSj x.1 ((mem_preds I).mp x.2)
    have hr := N.released j
    have : max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
      (fun x => kappa I x.1)) (I.r j) ≤ N.S j := max_le hsup hr
    linarith
  · have hr := N.released j
    linarith

theorem solution {n m : ℕ} (I : Instance n) :
    (∀ N : Schedule I m, ∑ i, I.w i * kappa I i ≤ N.wct) ∧
    ∃ N : Schedule I n, N.wct = ∑ i, I.w i * kappa I i := by
  refine ⟨?_, ?_⟩
  · intro N
    rw [Schedule.wct]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (kappa_le_C I m N j) (I.w_pos j).le
  · refine ⟨⟨fun j => kappa I j - I.p j, fun j => j, ?_, ?_, ?_⟩, ?_⟩
    · intro j
      have := pr_le_kappa I j
      linarith
    · intro i j hM hij
      exact absurd hM hij
    · intro i j hij
      have := kappa_prec I i j hij
      linarith
    · rw [Schedule.wct]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Schedule.C]
      ring
