-- Prove2me | solution 1 for BalasAdditive.Convergence.additive_algorithm_convergence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:33:25.439934+00:00
-- url     : https://prove2.me/submissions/5d15dbf1-b7cc-4ac9-9e23-f0dc092e817a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BalasAdditive_Convergence_Algorithm
import Theorems.Thm_BalasAdditive_Convergence_finite_steps_per_iteration
import Theorems.Thm_BalasAdditive_Convergence_no_solution_twice
import Theorems.Thm_BalasAdditive_Convergence_abandoned_no_better_completion

set_option autoImplicit false

namespace BalasAdditive.Convergence.RedAux

open BalasAdditive.Convergence
open Classical

theorem step_hist {n m : ℕ} (P : Problem n m) (σ τ : State n) (h : Step P σ τ) :
    τ.history = σ.history ∨ ∃ r, τ.history = σ.history ++ [r] := by
  cases h <;> first
    | (left; rfl)
    | (right; exact ⟨_, rfl⟩)

theorem reach_head {n m : ℕ} (P : Problem n m) (σ : State n) (hr : Reachable P σ) :
    ∃ r rest, σ.history = r :: rest ∧ r.J = ∅ := by
  induction hr with
  | refl => exact ⟨_, [], rfl, rfl⟩
  | @tail a b _ hs ih =>
    obtain ⟨r, rest, h1, h2⟩ := ih
    rcases step_hist P a b hs with h | ⟨r', h⟩
    · exact ⟨r, rest, by rw [h, h1], h2⟩
    · exact ⟨r, rest ++ [r'], by rw [h, h1]; rfl, h2⟩

theorem J_zero {n m : ℕ} (P : Problem n m) (σ : State n) (hr : Reachable P σ) :
    0 < σ.history.length ∧ σ.J 0 = ∅ := by
  obtain ⟨r, rest, h1, h2⟩ := reach_head P σ hr
  refine ⟨by simp [h1], ?_⟩
  simp [State.J, h1, h2]

/-- Fold facts about the ceiling. -/
theorem fold_le {n m : ℕ} (P : Problem n m) (xs : List (Finset (Fin n))) :
    ∀ z : WithTop ℝ,
      xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z ≤ z ∧
      (∀ x ∈ xs, P.lp.Feasible x →
        xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z
          ≤ (↑(P.lp.cost x) : WithTop ℝ)) ∧
      (xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z = z ∨
        ∃ x ∈ xs, P.lp.Feasible x ∧
          xs.foldl (fun z J => if P.lp.Feasible J then min z (↑(P.lp.cost J) : WithTop ℝ) else z) z
            = (↑(P.lp.cost x) : WithTop ℝ)) := by
  induction xs with
  | nil => intro z; simp
  | cons a t ih =>
    intro z
    simp only [List.foldl_cons]
    set z' := (if P.lp.Feasible a then min z (↑(P.lp.cost a) : WithTop ℝ) else z) with hz'
    obtain ⟨i1, i2, i3⟩ := ih z'
    have hz'le : z' ≤ z := by
      rw [hz']; split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    refine ⟨i1.trans hz'le, ?_, ?_⟩
    · intro x hx hf
      rcases List.mem_cons.mp hx with rfl | hx
      · refine i1.trans ?_
        rw [hz', if_pos hf]; exact min_le_right _ _
      · exact i2 x hx hf
    · rcases i3 with e | ⟨x, hx, hf, e⟩
      · rw [e, hz']
        by_cases ha : P.lp.Feasible a
        · rw [if_pos ha]
          rcases min_choice z (↑(P.lp.cost a) : WithTop ℝ) with h | h
          · left; exact h
          · right; exact ⟨a, List.mem_cons_self, ha, h⟩
        · left; rw [if_neg ha]
      · right; exact ⟨x, List.mem_cons_of_mem _ hx, hf, e⟩

theorem ceiling_le {n m : ℕ} (P : Problem n m) (σ : State n) (q : ℕ)
    (hq : q < σ.history.length) (hf : P.lp.Feasible (σ.J q)) :
    ceiling P σ ≤ (↑(P.lp.cost (σ.J q)) : WithTop ℝ) := by
  have hmem : σ.J q ∈ σ.history.map Record.J := by
    simp only [State.J, List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some]
    exact List.mem_map.mpr ⟨_, List.getElem_mem hq, rfl⟩
  exact (fold_le P _ ⊤).2.1 _ hmem hf

theorem ceiling_attained {n m : ℕ} (P : Problem n m) (σ : State n)
    (hne : ceiling P σ ≠ ⊤) :
    ∃ q, q < σ.history.length ∧ P.lp.Feasible (σ.J q) ∧
      (↑(P.lp.cost (σ.J q)) : WithTop ℝ) = ceiling P σ := by
  rcases (fold_le P (σ.history.map Record.J) ⊤).2.2 with e | ⟨x, hx, hf, e⟩
  · exact absurd e hne
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    obtain ⟨q, hq, hqr⟩ := List.getElem_of_mem hr
    refine ⟨q, hq, ?_, ?_⟩
    · simpa [State.J, List.getElem?_eq_getElem hq, hqr] using hf
    · have : σ.J q = r.J := by simp [State.J, List.getElem?_eq_getElem hq, hqr]
      rw [this]; exact e.symm

/-- At a reachable stopped state, no feasible assignment beats the ceiling. -/
theorem stopped_no_better {n m : ℕ} (P : Problem n m) (σ : State n)
    (hr : Reachable P σ) (hst : σ.phase = .stopped) (K : Finset (Fin n))
    (hK : P.lp.Feasible K) : ¬ (↑(P.lp.cost K) : WithTop ℝ) < ceiling P σ := by
  intro hlt
  obtain ⟨h0, hJ0⟩ := J_zero P σ hr
  by_cases hKe : K = ∅
  · subst hKe
    have := ceiling_le P σ 0 h0 (by rw [hJ0]; exact hK)
    rw [hJ0] at this
    exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl _)
  · have hab : Abandoned P σ 0 := ⟨h0, Or.inl hst⟩
    apply abandoned_no_better_completion P σ hr 0 hab
    refine ⟨K, hK, ?_, hlt⟩
    rw [hJ0]; exact Finset.nonempty_iff_ne_empty.mpr hKe |>.empty_ssubset

theorem chosen_exists {n m : ℕ} (P : Problem n m) (J X : Finset (Fin n))
    (hX : X.Nonempty) : ∃ j, Chosen P J X j := by
  obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image X (choiceValue P J) hX
  set Y := X.filter (fun q => choiceValue P J q = choiceValue P J j0)
  have hY : Y.Nonempty := ⟨j0, Finset.mem_filter.mpr ⟨hj0, rfl⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image Y (fun q => P.lp.c q) hY
  have hjX := (Finset.mem_filter.mp hj).1
  have hjv := (Finset.mem_filter.mp hj).2
  refine ⟨j, hjX, ?_, ?_⟩
  · intro q hq; rw [hjv]; exact hmax q hq
  · intro q hq hqv
    exact hmin q (Finset.mem_filter.mpr ⟨hq, by rw [hqv, hjv]⟩)

theorem selected_exists {n m : ℕ} (P : Problem n m) (σ : State n) (bound : ℕ)
    (h : ∃ k, Candidate P σ bound k) : ∃ k, Selected P σ bound k := by
  set S := (Finset.range bound).filter (fun k => Candidate P σ bound k)
  have hS : S.Nonempty := by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk.1, hk⟩⟩
  refine ⟨S.max' hS, (Finset.mem_filter.mp (S.max'_mem hS)).2, ?_⟩
  intro q hq
  exact S.le_max' q (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq.1, hq⟩)

theorem progress {n m : ℕ} (P : Problem n m) (σ : State n)
    (hne : σ.phase ≠ .stopped) : ∃ τ, Step P σ τ := by
  rcases hph : σ.phase with _ | bound | _
  · -- start
    by_cases hf : P.lp.Feasible σ.latest
    · exact ⟨_, Step.one_a σ hph hf⟩
    by_cases he : σ.N (σ.history.length - 1) = ∅
    · exact ⟨_, Step.two_a σ hph hf he⟩
    have hn := Finset.nonempty_iff_ne_empty.mpr he
    by_cases hh : relationsHold P σ.latest (σ.N (σ.history.length - 1))
    · by_cases hs : relationsStrict P σ.latest (σ.N (σ.history.length - 1))
      · obtain ⟨j, hj⟩ := chosen_exists P σ.latest _ hn
        exact ⟨_, Step.three_b σ j hph hf hn hs hj⟩
      · by_cases hc : belowCeiling P σ σ.latest
            (equalityF P σ.latest (σ.N (σ.history.length - 1)))
        · exact ⟨_, Step.four_a σ hph hf hn hh hs hc⟩
        · exact ⟨_, Step.four_b σ hph hf hn hh hs hc⟩
    · exact ⟨_, Step.three_a σ hph hf hn hh⟩
  · -- scan
    by_cases hc : ∃ k, Candidate P σ bound k
    · obtain ⟨k, hk⟩ := selected_exists P σ bound hc
      have hn : (oldRemaining P σ k).Nonempty := hk.1.2.2
      by_cases hh : relationsHold P (σ.J k) (oldRemaining P σ k)
      · by_cases hs : relationsStrict P (σ.J k) (oldRemaining P σ k)
        · obtain ⟨j, hj⟩ := chosen_exists P (σ.J k) _ hn
          exact ⟨_, Step.six_b σ bound k j hph hk hs hj⟩
        · by_cases hb : belowCeiling P σ (σ.J k) (equalityF P (σ.J k) (oldRemaining P σ k))
          · exact ⟨_, Step.seven_a σ bound k hph hk hh hs hb⟩
          · exact ⟨_, Step.seven_b σ bound k hph hk hh hs hb⟩
      · exact ⟨_, Step.six_a σ bound k hph hk hh⟩
    · exact ⟨_, Step.five_a σ bound hph hc⟩
  · exact absurd hph hne

theorem no_infinite_run {n m : ℕ} (P : Problem n m) :
    ¬ ∃ run : ℕ → State n, run 0 = init P ∧ ∀ t, Step P (run t) (run (t + 1)) := by
  rintro ⟨run, h0, hs⟩
  have hreach : ∀ t, Reachable P (run t) := by
    intro t; induction t with
    | zero => rw [h0]; exact Relation.ReflTransGen.refl
    | succ t ih => exact Relation.ReflTransGen.tail ih (hs t)
  set f : ℕ → ℕ := fun t => (run t).history.length with hf
  have hmono1 : ∀ t, f t ≤ f (t + 1) := by
    intro t
    rcases step_hist P _ _ (hs t) with h | ⟨r, h⟩
    · simp [hf, h]
    · simp [hf, h]
  have hmono : Monotone f := monotone_nat_of_le_succ hmono1
  have hbound : ∀ t, f t ≤ Fintype.card (Finset (Fin n)) := by
    intro t
    have := (no_solution_twice P (run t) (hreach t)).length_le_card
    simpa [hf] using this
  have hbdd : BddAbove (Set.range f) := ⟨_, by rintro _ ⟨t, rfl⟩; exact hbound t⟩
  obtain ⟨t0, ht0⟩ : sSup (Set.range f) ∈ Set.range f :=
    Nat.sSup_mem (Set.range_nonempty f) hbdd
  have hconst : ∀ t, f (t0 + t) = f t0 := by
    intro t
    apply le_antisymm
    · rw [ht0]; exact le_csSup hbdd ⟨_, rfl⟩
    · exact hmono (Nat.le_add_right _ _)
  apply finite_steps_per_iteration P (run t0) (hreach t0)
  refine ⟨fun t => run (t0 + t), by simp, ?_, ?_⟩
  · intro t; exact hs (t0 + t)
  · intro t; exact hconst t

end BalasAdditive.Convergence.RedAux

open BalasAdditive.Convergence

theorem solution {n m : ℕ} (P : Problem n m) :
    (¬ ∃ run : ℕ → State n,
      run 0 = init P ∧ ∀ t, Step P (run t) (run (t + 1))) ∧
    (∀ σ : State n, Reachable P σ → σ.phase ≠ .stopped → ∃ τ, Step P σ τ) ∧
    (∀ σ : State n, Reachable P σ → σ.phase = .stopped →
      (ceiling P σ = ⊤ → ∀ J : Finset (Fin n), ¬ P.lp.Feasible J) ∧
      (ceiling P σ ≠ ⊤ →
        (∃ q, q < σ.history.length ∧ P.lp.Feasible (σ.J q) ∧
          (↑(P.lp.cost (σ.J q)) : WithTop ℝ) = ceiling P σ) ∧
        (∀ q, q < σ.history.length → P.lp.Feasible (σ.J q) →
          (↑(P.lp.cost (σ.J q)) : WithTop ℝ) = ceiling P σ →
          P.lp.Optimal (σ.J q)))) := by
  refine ⟨RedAux.no_infinite_run P, fun σ _ hne => RedAux.progress P σ hne, ?_⟩
  intro σ hr hst
  refine ⟨?_, ?_⟩
  · intro htop J hJ
    apply RedAux.stopped_no_better P σ hr hst J hJ
    rw [htop]; exact WithTop.coe_lt_top _
  · intro _
    refine ⟨RedAux.ceiling_attained P σ ‹_›, ?_⟩
    intro q _ hf heq
    refine ⟨hf, fun K hK => ?_⟩
    have h := RedAux.stopped_no_better P σ hr hst K hK
    rw [not_lt, ← heq] at h
    exact WithTop.coe_le_coe.mp h
