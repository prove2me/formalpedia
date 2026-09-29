-- Prove2me | solution 1 for AvgCompletionSched.DelayList.kappa_prime_le_kappa
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:40:00.010996+00:00
-- url     : https://prove2.me/submissions/0f2d7da7-db1f-4f15-9150-1e1bc86e6c27

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm
import Definitions.Def_AvgCompletionSched_DelayList_Analysis

namespace AvgCompletionSched.DelayList

theorem aux_kpl_kappa_eq {n : ℕ} (I : Instance n) (j : Fin n) :
    kappa I j =
      if h : (I.preds j).Nonempty then
        I.p j + max ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
          fun i => kappa I i.1) (I.r j)
      else I.p j + I.r j := by
  unfold kappa
  rw [WellFounded.fix_eq]

theorem aux_kpl_ge {n : ℕ} (I : Instance n) (j : Fin n) : I.p j + I.r j ≤ kappa I j := by
  rw [aux_kpl_kappa_eq]
  split_ifs with h
  · have := le_max_right ((I.preds j).attach.sup' (Finset.attach_nonempty_iff.mpr h)
          fun i => kappa I i.1) (I.r j)
    linarith
  · exact le_refl _

theorem aux_kpl_prec {n : ℕ} (I : Instance n) (a b : Fin n) (hab : I.prec a b) :
    kappa I a + I.p b ≤ kappa I b := by
  have ha : a ∈ I.preds b := by simp [Instance.preds, hab]
  have hne : (I.preds b).Nonempty := ⟨a, ha⟩
  rw [aux_kpl_kappa_eq I b, dif_pos hne]
  have h1 : kappa I a ≤ (I.preds b).attach.sup' (Finset.attach_nonempty_iff.mpr hne)
      (fun i => kappa I i.1) :=
    Finset.le_sup' (f := fun i : {x // x ∈ I.preds b} => kappa I i.1)
      (Finset.mem_attach _ ⟨a, ha⟩)
  have h2 := le_max_left ((I.preds b).attach.sup' (Finset.attach_nonempty_iff.mpr hne)
      (fun i => kappa I i.1)) (I.r b)
  linarith

theorem aux_kpl_chain {n m : ℕ} (I : Instance n) (D : DelayListRun I m) :
    ∀ (l : List (Fin n)) (a : Fin n), List.IsChain D.PathStep (a :: l) →
      kappa I a + (l.map I.p).sum ≤ kappa I ((a :: l).getLast (List.cons_ne_nil _ _)) := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons b l ih =>
    intro a h
    rw [List.isChain_cons_cons] at h
    obtain ⟨hab, hrest⟩ := h
    have h1 := ih b hrest
    have h2 := aux_kpl_prec I a b hab.1
    rw [List.getLast_cons_cons]
    simp only [List.map_cons, List.sum_cons]
    linarith

end AvgCompletionSched.DelayList

open AvgCompletionSched.DelayList

theorem solution {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (π : Fin n ≃ Fin n)
    (hπ : ObeysPrecedence I π) (β : ℝ) (hβ : 0 < β) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (i j₁ : Fin n) (l : List (Fin n))
    (hP : D.IsPathPrime i j₁ l) :
    kappaPrime I j₁ l ≤ kappa I i := by
  obtain ⟨hlast, hchain, _⟩ := hP
  have h1 := aux_kpl_chain I D l j₁ hchain
  rw [hlast] at h1
  have h2 := aux_kpl_ge I j₁
  unfold kappaPrime
  simp only [List.map_cons, List.sum_cons]
  linarith
