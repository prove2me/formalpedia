-- Prove2me | solution 1 for CarbonDoubleCount.Leader.pf_le_pe
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:36:14.344639+00:00
-- url     : https://prove2.me/submissions/d603b9b4-11d9-43d5-88f7-36f47386ca18

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
    ∀ (g : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ),
      PFFeasible A V f L πbar g e → pfObjective V f p L g e ≤ peObjective V f p L gE eE := by
  intro g e hF
  have key : PEFeasible A V L πbar (fun n x => g n (f (Function.update e n x))) e := by
    refine ⟨hF.1, ?_, ?_⟩
    · intro n hn
      simpa [Function.update_eq_self] using hF.2.1 n hn
    · intro n hn x hx
      simpa [Function.update_eq_self] using hF.2.2 n hn x hx
  have h := hopt.2 _ e key
  have heq : peObjective V f p L (fun n x => g n (f (Function.update e n x))) e
      = pfObjective V f p L g e := by
    unfold peObjective pfObjective
    simp [Function.update_eq_self]
  linarith
