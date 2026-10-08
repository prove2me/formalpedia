-- Prove2me | solution 1 for FibHeap.Amort.potential_decreaseKey_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:57:00.85915+00:00
-- url     : https://prove2.me/submissions/bfe52529-13dc-4fe1-8683-111ec5230892

import Mathlib
import Definitions.Def_FibHeap_Amort_Model



namespace FibHeap.Amort
open FTree

def hpot (r : Heap) : ℕ := r.length + 2 * markedNonroot r

theorem potential_eq (s : Coll) : potential s = (s.map hpot).sum := rfl

theorem pot_set (s : Coll) (h : ℕ) (r r' : Heap) (hs : s[h]? = some r) :
    potential (s.set h r') + hpot r = potential s + hpot r' := by
  induction s generalizing h with
  | nil => simp at hs
  | cons a s ih =>
    cases h with
    | zero =>
      simp at hs; subst hs
      simp [potential_eq]; ring
    | succ h =>
      simp at hs
      have := ih h hs
      simp only [potential_eq, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

theorem hpot_append (r r' : Heap) : hpot (r ++ r') = hpot r + hpot r' := by
  simp [hpot, markedNonroot, List.map_append, List.sum_append]; ring

/-- sum of children marked counts -/
def Pc (t : FTree) : ℕ := (t.children.map markedCount).sum
def rho (t : FTree) : ℕ := 1 + 2 * Pc t

theorem mc_eq (t : FTree) : markedCount t = (if t.marked then 1 else 0) + Pc t := by
  cases t; simp only [markedCount, Pc, FTree.marked, FTree.children]
  rfl

theorem mc_setMarked_true (t : FTree) (h : t.marked = false) :
    markedCount (t.setMarked true) = markedCount t + 1 := by
  cases t; simp [markedCount, FTree.setMarked, FTree.marked] at *; subst h; simp; ring

theorem Pc_setKey (t : FTree) (k : ℝ) : Pc (t.setKey k) = Pc t := by
  cases t; simp [Pc, FTree.setKey, FTree.children]

theorem mc_setKey (t : FTree) (k : ℝ) : markedCount (t.setKey k) = markedCount t := by
  cases t; simp [markedCount, FTree.setKey]

theorem cut_marked {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost) : t'.marked = t.marked := by
  cases h <;> rfl

theorem cut_bound {i : ℕ} {f : FTree → List FTree} {t t' : FTree} {R : List FTree} {n : ℕ}
    {lost : Bool} (h : CutAt i f t t' R n lost)
    (hf : ∀ c, ((f c).map rho).sum ≤ 2 * markedCount c + 1) :
    (lost = true → 2 * markedCount t' + (R.map rho).sum + n ≤ 2 * markedCount t + 1) ∧
    (lost = false → 2 * markedCount t' + (R.map rho).sum + n ≤ 2 * markedCount t + 3) := by
  induction h with
  | direct hc =>
    rename_i it k m pre post c
    have := hf c
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨fun _ => by omega, by simp⟩
  | markParent hc hm ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.1 rfl
    have hm' := cut_marked hc
    have := mc_setMarked_true c' (by rw [hm', hm])
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨by simp, fun _ => by omega⟩
  | cascade hc hm ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.1 rfl
    have hm' := cut_marked hc
    have e1 := mc_eq c'
    have e2 := mc_eq c
    have e3 : rho c' + 1 = 2 * markedCount c' := by
      rw [e1, hm', hm]; simp [rho]; ring
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil]
    refine ⟨fun _ => by omega, by simp⟩
  | pass hc ih =>
    rename_i it k m pre post c c' R n
    have ih1 := ih.2 rfl
    simp only [markedCount, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    refine ⟨by simp, fun _ => by omega⟩

theorem hpot_eq (r : Heap) : hpot r = (r.map rho).sum := by
  induction r with
  | nil => simp [hpot, markedNonroot]
  | cons a r ih =>
    simp only [hpot, markedNonroot, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    simp only [rho, Pc] at *
    omega

theorem dk_core (s s' : Coll) (Δ : ℝ) (i h : ℕ) (d : StepData)
    (hstep : Step s (.decreaseKey Δ i h) s' d) :
    potential s' + d.cascading ≤ potential s + 3 := by
  generalize ho : Op.decreaseKey Δ i h = op at hstep
  cases hstep <;> simp at ho
  case decreaseKeyRoot h' pre post x Δ' i' _ hs hx =>
    have := pot_set s h' _ (pre ++ x.setKey (x.key - Δ') :: post) hs
    have e : rho (x.setKey (x.key - Δ')) = rho x := by simp [rho, Pc_setKey]
    simp only [hpot_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, e] at this
    simp only [StepData.zero]
    omega
  case decreaseKeyCut h' pre post τ τ' R n lost Δ' i' _ hs hne hcut =>
    have := pot_set s h' _ (pre ++ τ' :: post ++ R) hs
    have hb := cut_bound hcut (by
      intro c
      have := mc_eq c
      simp [rho, Pc_setKey]
      omega)
    have hm := cut_marked hcut
    have e1 := mc_eq τ
    have e2 := mc_eq τ'
    simp only [hpot_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons] at this
    simp only [rho] at this
    have : rho τ' + 2 * markedCount τ = rho τ + 2 * markedCount τ' := by
      rw [e1, e2, hm]; simp [rho]; split <;> omega
    cases lost
    · have := hb.2 rfl; simp only [List.length_append, hpot_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rho] at *; omega
    · have := hb.1 rfl; simp only [List.length_append, hpot_eq, List.map_append, List.map_cons, List.sum_append, List.sum_cons, rho] at *; omega

end FibHeap.Amort

open FibHeap.Amort


theorem solution (s s' : Coll) (Δ : ℝ) (i h : ℕ) (d : StepData)
    (hstep : Step s (.decreaseKey Δ i h) s' d) :
    potential s' + d.cascading ≤ potential s + 3 := by
  exact dk_core s s' Δ i h d hstep
