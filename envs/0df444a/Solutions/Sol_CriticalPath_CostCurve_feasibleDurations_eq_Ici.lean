-- Prove2me | solution 1 for CriticalPath.CostCurve.feasibleDurations_eq_Ici
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:32:24.467669+00:00
-- url     : https://prove2.me/submissions/e40eaa7f-1810-4cd4-ad31-3f93438327c7

import Mathlib
import Definitions.Def_CriticalPath_CostCurve_ProjectNetwork
import Definitions.Def_CriticalPath_CostCurve_earliest
import Definitions.Def_CriticalPath_CostCurve_JobData
import Definitions.Def_CriticalPath_CostCurve_Schedule



namespace CriticalPath.CostCurve

variable {n : ℕ}

lemma earliest_eq' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) (j : Fin (n+1)) :
    earliest N y j = if h : (preds N j).Nonempty then
      (preds N j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
        (fun i => y i.1 j + earliest N y i.1)
    else 0 := by
  rw [earliest]

lemma mem_preds' (N : ProjectNetwork n) {i j : Fin (n+1)} (h : (i, j) ∈ N.P) : i ∈ preds N j := by
  simp [preds, N.label_lt _ h, h]

lemma le_earliest' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) {i j : Fin (n+1)}
    (h : (i, j) ∈ N.P) : y i j + earliest N y i ≤ earliest N y j := by
  have hm := mem_preds' N h
  have hne : (preds N j).Nonempty := ⟨i, hm⟩
  rw [earliest_eq' N y j, dif_pos hne]
  exact Finset.le_sup' (fun i : (preds N j) => y i.1 j + earliest N y i.1) (Finset.mem_attach _ ⟨i, hm⟩)

lemma earliest_zero' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ) :
    earliest N y 0 = 0 := by
  rw [earliest_eq', dif_neg]
  rintro ⟨i, hi⟩
  simp [preds] at hi

lemma earliest_le_of' (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (t : Fin (n+1) → ℝ) (hy : ∀ e ∈ N.P, y e.1 e.2 ≤ t e.2 - t e.1) (ht : ∀ j, t 0 ≤ t j) :
    ∀ j, earliest N y j ≤ t j - t 0 := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  rw [earliest_eq']
  split_ifs with hne
  · apply Finset.sup'_le
    rintro ⟨i, hi⟩ _
    have hi' := Finset.mem_filter.mp hi
    have h1 := ih i hi'.2.1
    have h2 := hy (i, j) hi'.2.2
    simp only at h2 ⊢
    linarith
  · linarith [ht j]

lemma earliest_mono' (N : ProjectNetwork n) (y y' : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hy : ∀ e ∈ N.P, y e.1 e.2 ≤ y' e.1 e.2) : ∀ j, earliest N y j ≤ earliest N y' j := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  rw [earliest_eq' N y j]
  split_ifs with hne
  · apply Finset.sup'_le
    rintro ⟨i, hi⟩ _
    have hi' := Finset.mem_filter.mp hi
    have h1 := ih i hi'.2.1
    have h2 := hy (i, j) hi'.2.2
    have h3 := le_earliest' N y' hi'.2.2
    simp only at h2 ⊢
    linarith
  · rw [earliest_eq' N y' j, dif_neg hne]

lemma earliest_continuous' (N : ProjectNetwork n) (Y : ℝ → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hY : ∀ i j, Continuous (fun s => Y s i j)) : ∀ j, Continuous (fun s => earliest N (Y s) j) := by
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih =>
  simp_rw [earliest_eq' N _ j]
  split_ifs with hne
  · apply Continuous.finset_sup'_apply
    rintro ⟨i, hi⟩ _
    exact (hY i j).add (ih i (Finset.mem_filter.mp hi).2.1)
  · exact continuous_const

lemma sched_mono' {N : ProjectNetwork n} (J : JobData N) {lam : ℝ} {y t}
    (h : IsSchedule J lam y t) {a b : Fin (n+1)}
    (hab : Relation.ReflTransGen (fun i j => (i, j) ∈ N.P) a b) : t a ≤ t b := by
  induction hab with
  | refl => exact le_rfl
  | tail _ he ih =>
    have h1 := h.2.1 _ he
    have h2 := (h.1 _ he).1
    have h3 := J.crash_nonneg _ he
    simp only at h1 h2 h3
    linarith

lemma sched_bounds' {N : ProjectNetwork n} (J : JobData N) {lam : ℝ} {y t}
    (h : IsSchedule J lam y t) (j : Fin (n+1)) : 0 ≤ t j ∧ t j ≤ lam := by
  have h1 := sched_mono' J h (N.origin_precedes j)
  have h2 := sched_mono' J h (N.terminus_follows j)
  rw [h.2.2.1] at h1; rw [h.2.2.2] at h2
  exact ⟨h1, h2⟩

lemma last_ne_zero' (N : ProjectNetwork n) : (Fin.last n) ≠ 0 := by
  have := N.one_le
  intro h
  have := congrArg Fin.val h
  simp at this; omega

lemma feasible_core {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    feasibleDurations J = Set.Ici (earliest N J.d (Fin.last n)) := by
  ext lam
  constructor
  · rintro ⟨y, t, h⟩
    have hy : ∀ e ∈ N.P, J.d e.1 e.2 ≤ t e.2 - t e.1 := fun e he =>
      le_trans (h.1 e he).1 (h.2.1 e he)
    have := earliest_le_of' N J.d t hy (fun j => by rw [h.2.2.1]; exact (sched_bounds' J h j).1)
      (Fin.last n)
    rw [h.2.2.1, h.2.2.2] at this
    simp only [Set.mem_Ici]; linarith
  · intro hl
    simp only [Set.mem_Ici] at hl
    refine ⟨J.d, fun j => if j = Fin.last n then lam else earliest N J.d j, ?_, ?_, ?_, ?_⟩
    · intro e he; exact ⟨le_rfl, J.crash_le_normal e he⟩
    · intro e he
      have hlt := N.label_lt e he
      have h1 : e.1 ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hlt (Fin.le_last _))
      have h2 := le_earliest' N J.d (i := e.1) (j := e.2) he
      simp only [h1, if_false]
      split_ifs with h3
      · rw [h3] at h2 ⊢; linarith
      · linarith
    · simp [Ne.symm (last_ne_zero' N), earliest_zero']
    · simp

end CriticalPath.CostCurve

open CriticalPath.CostCurve


theorem solution {n : ℕ} (N : ProjectNetwork n) (J : JobData N) :
    feasibleDurations J = Set.Ici (earliest N J.d (Fin.last n)) := by
  exact feasible_core N J
