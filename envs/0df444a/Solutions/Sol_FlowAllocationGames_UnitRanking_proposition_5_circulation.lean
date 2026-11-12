-- Prove2me | solution 1 for FlowAllocationGames.UnitRanking.proposition_5_circulation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:56:39.866192+00:00
-- url     : https://prove2.me/submissions/533123ea-e51d-491d-a7af-dee57e8afb89

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_cplus

open scoped NNReal

open FlowAllocationGames.UnitRanking in
theorem solution {n m : ℕ} (Γ : Game n m) (a : Fin m → ℝ≥0 → ℝ≥0)
    (hcap : ∀ e y, a e y ≤ Γ.c e)
    (hnf : ∀ v y, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), a e y =
      min (cplus Γ v : ℝ≥0) y)
    (f : Fin m → ℝ≥0)
    (hf : ∀ e, f e = a e ((Γ.b (Γ.tail e) : ℝ≥0) +
      ∑ e' ∈ Finset.univ.filter (fun e' => Γ.head e' = Γ.tail e), f e')) :
    (∀ v, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e ≤
      (Γ.b v : ℝ≥0) + ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e) ∧
    (∀ e, f e ≤ Γ.c e) ∧
    ∑ v, ((Γ.b v : ℝ≥0) + ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e -
      ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e) = ∑ v, (Γ.b v : ℝ≥0) := by
  have hout : ∀ v, ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e ≤
      (Γ.b v : ℝ≥0) + ∑ e ∈ Finset.univ.filter (fun e => Γ.head e = v), f e := by
    intro v
    have h1 : ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v), f e =
        ∑ e ∈ Finset.univ.filter (fun e => Γ.tail e = v),
          a e ((Γ.b v : ℝ≥0) + ∑ e' ∈ Finset.univ.filter (fun e' => Γ.head e' = v), f e') := by
      apply Finset.sum_congr rfl
      intro e he
      have hv : Γ.tail e = v := (Finset.mem_filter.1 he).2
      rw [hf e, hv]
    rw [h1, hnf]
    exact min_le_right _ _
  refine ⟨hout, fun e => (hf e).symm ▸ hcap _ _, ?_⟩
  rw [Finset.sum_tsub_distrib _ (fun v _ => hout v), Finset.sum_add_distrib,
    Finset.sum_fiberwise Finset.univ Γ.head f, Finset.sum_fiberwise Finset.univ Γ.tail f,
    add_tsub_cancel_right]
