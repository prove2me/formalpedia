-- Prove2me | solution 1 for CarbonDoubleCount.Leader.pe_reduction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:55:44.117354+00:00
-- url     : https://prove2.me/submissions/58aa590c-b477-47ad-a23a-8632938bb041

import Mathlib
import Definitions.Def_CarbonDoubleCount_Leader_Setting

open CarbonDoubleCount.Leader

open Finset

theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {act : ι → Type} [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (A p : ℝ)
    (V : (n : ι) → (act n → ℝ) → ℝ) (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (L : ι) (πbar : ι → ℝ)
    (gE : (n : ι) → (act n → ℝ) → ℝ) (eE : (n : ι) → act n → ℝ)
    (hopt : IsOptimalPE A V f p L πbar gE eE) :
    peObjective V f p L gE eE = socialValue V f p eE - ∑ n ∈ univ.erase L, πbar n ∧
      ∀ e ∈ CarbonDoubleCount.Planner.effortBox A, socialValue V f p e ≤ socialValue V f p eE := by
  have key : ∀ e, peObjective V f p L (fun n x => V n x - πbar n) e
      = socialValue V f p e - ∑ n ∈ univ.erase L, πbar n := by
    intro e
    unfold peObjective socialValue
    rw [← Finset.add_sum_erase univ (fun n => V n (e n)) (mem_univ L), Finset.sum_sub_distrib]
    ring
  have feas : ∀ e ∈ CarbonDoubleCount.Planner.effortBox A,
      PEFeasible A V L πbar (fun n x => V n x - πbar n) e := by
    intro e he
    refine ⟨he, fun n _ => by simp, fun n _ x _ => by simp⟩
  have hle : peObjective V f p L gE eE ≤ socialValue V f p eE - ∑ n ∈ univ.erase L, πbar n := by
    rw [← key]
    unfold peObjective
    have : ∑ n ∈ univ.erase L, gE n (eE n) ≤ ∑ n ∈ univ.erase L, (V n (eE n) - πbar n) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      have := hopt.1.2.1 n (Finset.ne_of_mem_erase hn)
      linarith
    linarith
  have hge := hopt.2 _ eE (feas eE hopt.1.1)
  rw [key] at hge
  have h1 : peObjective V f p L gE eE = socialValue V f p eE - ∑ n ∈ univ.erase L, πbar n :=
    le_antisymm hle hge
  refine ⟨h1, fun e he => ?_⟩
  have := hopt.2 _ e (feas e he)
  rw [key, h1] at this
  linarith
