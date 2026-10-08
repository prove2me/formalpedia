-- Prove2me | solution 1 for DoubleGreedyUSM.Fractional.opt_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:00:07.03769+00:00
-- url     : https://prove2.me/submissions/e01ea7e3-3ce2-4164-afba-717a52b1987b

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4

set_option autoImplicit false

namespace A7c08d19

open DoubleGreedyUSM.Fractional

lemma tr_sum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if a + b = 0 then (1 : ℝ) else a / (a + b)) + (if a + b = 0 then (0 : ℝ) else b / (a + b)) = 1 := by
  split_ifs with h
  · norm_num
  · rw [← add_div, div_self h]

lemma step_diff {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : (X → ℝ) × (X → ℝ)) (u v : X) :
    (step f s u).2 v - (step f s u).1 v = s.2 v - s.1 v - indicator {u} v := by
  have key := tr_sum (max (aGain f s.1 u) 0) (max (bGain f s.2 u) 0)
    (le_max_right _ _) (le_max_right _ _)
  simp only [step, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(indicator {u} v)) * key

lemma fold_diff {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) :
    ∀ (l : List X) (s : (X → ℝ) × (X → ℝ)) (L : List X), l.Nodup → (∀ u ∈ l, u ∉ L) →
      (∀ v, s.2 v - s.1 v = if v ∈ L then 0 else 1) →
      ∀ v, (l.foldl (step f) s).2 v - (l.foldl (step f) s).1 v =
        if v ∈ L ∨ v ∈ l then 0 else 1 := by
  intro l
  induction l with
  | nil =>
    intro s L _ _ hs v
    simpa using hs v
  | cons u l ih =>
    intro s L hnd hdis hs v
    rw [List.nodup_cons] at hnd
    rw [List.foldl_cons]
    have h1 : ∀ w ∈ l, w ∉ u :: L := by
      intro w hw hwL
      rcases List.mem_cons.mp hwL with h | h
      · exact hnd.1 (h ▸ hw)
      · exact hdis w (List.mem_cons_of_mem u hw) h
    have h2 : ∀ w, (step f s u).2 w - (step f s u).1 w = if w ∈ u :: L then 0 else 1 := by
      intro w
      rw [step_diff, hs w]
      have huL : u ∉ L := hdis u (List.mem_cons_self)
      by_cases hwu : w = u
      · subst hwu
        simp [indicator, huL]
      · simp [indicator, hwu]
    rw [ih (step f s u) (u :: L) hnd.2 h1 h2 v]
    have : (v ∈ u :: L ∨ v ∈ l) ↔ (v ∈ L ∨ v ∈ u :: l) := by
      simp only [List.mem_cons]
      tauto
    simp only [this]

end A7c08d19

open DoubleGreedyUSM.Fractional in
theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f)
    (l : List X) (hl : l.Nodup) (hcov : ∀ x, x ∈ l)
    (O : Finset X) (hO : ∀ S : Finset X, f S ≤ f O) :
    optI O (state f l 0) = indicator O ∧
    NonmonotoneSubmod.Shared.F f (indicator O) = f O ∧
    optI O (state f l l.length) = (state f l l.length).1 ∧
    (state f l l.length).1 = (state f l l.length).2 := by
  have hfin : (state f l l.length).1 = (state f l l.length).2 := by
    funext v
    have h := A7c08d19.fold_diff f l (0, 1) [] hl (by simp) (by intro v; simp) v
    have hs : state f l l.length = l.foldl (step f) (0, 1) := by
      simp [state, List.take_length]
    rw [hs]
    simp only [List.not_mem_nil, false_or, hcov v, if_true] at h
    linarith
  refine ⟨?_, ?_, ?_, hfin⟩
  · have h0 : state f l 0 = (0, 1) := by simp [state]
    rw [h0]
    funext v
    simp only [optI, indicator, Pi.zero_apply, Pi.one_apply]
    split_ifs <;> norm_num
  · unfold NonmonotoneSubmod.Shared.F
    rw [Finset.sum_eq_single O]
    · have : ∀ i : X, (if i ∈ O then indicator O i else 1 - indicator O i) = 1 := by
        intro i
        by_cases hi : i ∈ O <;> simp [indicator, hi]
      simp [this]
    · intro S _ hSO
      apply mul_eq_zero_of_right
      have : ∃ i, ¬ (i ∈ S ↔ i ∈ O) := by
        by_contra hc
        exact hSO (Finset.ext fun i => by
          by_contra h
          exact hc ⟨i, h⟩)
      obtain ⟨i, hi⟩ := this
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      by_cases hiS : i ∈ S
      · have hiO : i ∉ O := fun h => hi ⟨fun _ => h, fun _ => hiS⟩
        simp [indicator, hiS, hiO]
      · have hiO : i ∈ O := by
          by_contra h
          exact hi ⟨fun h' => absurd h' hiS, fun h' => absurd h' h⟩
        simp [indicator, hiS, hiO]
    · intro h
      exact absurd (Finset.mem_univ O) h
  · funext v
    simp only [optI]
    rw [← hfin]
    exact min_eq_right (le_max_right _ _)
