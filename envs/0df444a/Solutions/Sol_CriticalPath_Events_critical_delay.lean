-- Prove2me | solution 1 for CriticalPath.Events.critical_delay
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:43:09.678877+00:00
-- url     : https://prove2.me/submissions/78e548a5-25c6-4f97-a6ba-bb09fb55c213

import Mathlib
import Definitions.Def_CriticalPath_Events_ProjectNetwork
import Definitions.Def_CriticalPath_Events_EventTimes

set_option autoImplicit false

namespace CriticalPath.Events

namespace CDelayAux

theorem earliest_unfold {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    earliest N y j = (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty hj))
      (fun i => y i.1 j + earliest N y i.1) := by
  rw [earliest]
  simp [hj]

theorem latest_unfold {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    latest N y lam i = (N.succ i).attach.inf' (Finset.attach_nonempty_iff.2 (N.succ_nonempty hi))
      (fun j => latest N y lam j.1 - y i j.1) := by
  rw [latest]
  simp [hi]

theorem earliest_le_of_mem {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) (h : (i, j) ∈ N.P) :
    y i j + earliest N y i ≤ earliest N y j := by
  have hj : j ≠ 0 := by
    intro h0
    have := N.label_lt (i, j) h
    simp [h0] at this
  rw [earliest_unfold N y j hj]
  exact Finset.le_sup' (fun i : N.pred j => y i.1 j + earliest N y i.1)
    (Finset.mem_attach _ ⟨i, (N.mem_pred).2 h⟩)

/-- Earliest times agree at events not after the tail of `e`. -/
theorem agree {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) (he : e ∈ N.P) (δ : ℝ) :
    ∀ m : ℕ, ∀ j : Fin (n + 1), j.val = m → j ≤ e.1 →
      earliest N (fun a b => if (a, b) = e then y a b + δ else y a b) j = earliest N y j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hjm hje
    by_cases hj : j = 0
    · subst hj
      rw [earliest, earliest]
      simp
    rw [earliest_unfold N _ j hj, earliest_unfold N y j hj]
    apply Finset.sup'_congr _ rfl
    intro i _
    have hij : i.1 < j := N.lt_of_mem_pred i.2
    have hne : (i.1, j) ≠ e := by
      intro h
      have hlt : e.1 < e.2 := N.label_lt e he
      have h2 : e.2 = j := by rw [← h]
      rw [h2] at hlt
      exact lt_irrefl _ (lt_of_le_of_lt hje hlt)
    have hrec := ih i.1.val (by rw [← hjm]; exact hij) i.1 rfl (le_of_lt (lt_of_lt_of_le hij hje))
    simp only [hne, if_false, hrec]

/-- Upper bound: the delay raises every earliest time by at most `δ`. -/
theorem upper {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (e : Fin (n + 1) × Fin (n + 1)) (he : e ∈ N.P) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∀ m : ℕ, ∀ j : Fin (n + 1), j.val = m →
      earliest N (fun a b => if (a, b) = e then y a b + δ else y a b) j ≤ earliest N y j + δ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hjm
    by_cases hj : j = 0
    · subst hj
      rw [earliest, earliest]
      simpa using hδ
    rw [earliest_unfold N _ j hj, earliest_unfold N y j hj]
    apply Finset.sup'_le
    intro i hi
    have hij : i.1 < j := N.lt_of_mem_pred i.2
    have hle : y i.1 j + earliest N y i.1 ≤
        (N.pred j).attach.sup' (Finset.attach_nonempty_iff.2 (N.pred_nonempty hj))
          (fun i => y i.1 j + earliest N y i.1) :=
      Finset.le_sup' (fun i : N.pred j => y i.1 j + earliest N y i.1) hi
    by_cases hne : (i.1, j) = e
    · have hagree := agree N y e he δ i.1.val i.1 rfl (by rw [← hne])
      simp only [hne, if_true, hagree]
      linarith
    · have hrec := ih i.1.val (by rw [← hjm]; exact hij) i.1 rfl
      simp only [hne, if_false]
      linarith

/-- Path-to-terminus lower bound for any durations dominating `y`. -/
theorem tail_bound {n : ℕ} (N : ProjectNetwork n) (y y' : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hyy : ∀ a b, y a b ≤ y' a b) (L : ℝ) :
    ∀ m : ℕ, ∀ i : Fin (n + 1), n - i.val = m →
      L - latest N y L i ≤ earliest N y' (Fin.last n) - earliest N y' i := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i him
    by_cases hi : i = Fin.last n
    · subst hi
      rw [latest]
      simp
    rw [latest_unfold N y L i hi]
    obtain ⟨j, -, hjeq⟩ := Finset.exists_mem_eq_inf'
      (Finset.attach_nonempty_iff.2 (N.succ_nonempty hi))
      (fun j : N.succ i => latest N y L j.1 - y i j.1)
    rw [hjeq]
    have hij : i < j.1 := N.lt_of_mem_succ j.2
    have hjle : j.1.val ≤ n := Nat.lt_succ_iff.mp j.1.isLt
    have hlt : n - j.1.val < m := by
      rw [← him]; rw [Fin.lt_def] at hij; omega
    have hrec := ih _ hlt j.1 rfl
    have hedge := earliest_le_of_mem N y' i j.1 ((N.mem_succ).1 j.2)
    have hy := hyy i j.1
    linarith

end CDelayAux

end CriticalPath.Events

open CriticalPath.Events in
theorem solution {n : ℕ} (N : ProjectNetwork n) (y : Fin (n + 1) → Fin (n + 1) → ℝ)
    (lam : ℝ) (hlam : earliest N y (Fin.last n) ≤ lam)
    (e : Fin (n + 1) × Fin (n + 1)) (he : e ∈ N.P) (hcrit : IsCritical N y lam e)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    earliest N (fun a b => if (a, b) = e then y a b + δ else y a b) (Fin.last n) =
      earliest N y (Fin.last n) + δ := by
  set y' : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun a b => if (a, b) = e then y a b + δ else y a b with hy'
  apply le_antisymm
  · exact CDelayAux.upper N y e he δ hδ _ (Fin.last n) rfl
  · have hyy : ∀ a b, y a b ≤ y' a b := by
      intro a b
      simp only [hy']
      split_ifs <;> linarith
    have htail := CDelayAux.tail_bound N y y' hyy lam _ e.2 rfl
    have hedge := CDelayAux.earliest_le_of_mem N y' e.1 e.2 he
    have hye : y' e.1 e.2 = y e.1 e.2 + δ := by simp [hy']
    have hag : earliest N y' e.1 = earliest N y e.1 :=
      CDelayAux.agree N y e he δ _ e.1 rfl le_rfl
    have hc : latest N y lam e.2 - earliest N y e.1 = y e.1 e.2 := hcrit
    linarith
