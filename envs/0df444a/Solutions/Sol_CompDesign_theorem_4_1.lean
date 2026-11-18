-- Prove2me | solution 1 for CompDesign.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:37:55.618204+00:00
-- url     : https://prove2.me/submissions/1ee202ff-38b6-4f3a-bfa1-a27d3a916483

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesign_IsStrictImprovement
import Definitions.Def_CompDesign_PhiLex
import Theorems.Thm_CompDesign_thm_4_1_potential_increases
import Theorems.Thm_CompDesign_thm_4_1_terminal_is_pne

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (hcB : ∀ i, c i < B) :
    (¬ ∃ f : ℕ → Finset (Fin n), ∀ t, CompDesign.IsStrictImprovement v B c (f t) (f (t + 1))) ∧
    ∃ S : Finset (Fin n), IsPNE v B c S := by
  have hno : ¬ ∃ f : ℕ → Finset (Fin n), ∀ t, CompDesign.IsStrictImprovement v B c (f t) (f (t + 1)) := by
    rintro ⟨f, hf⟩
    have hmono : StrictMono (fun t => CompDesign.PhiLex v B c (f t)) :=
      strictMono_nat_of_lt_succ fun t =>
        CompDesign.thm_4_1_potential_increases v B c hB hv0 hm hs hc hcB (f t) (f (t + 1)) (hf t)
    have hinj : Function.Injective f := fun a b hab => hmono.injective (by simp only [hab])
    exact not_injective_infinite_finite f hinj
  refine ⟨hno, ?_⟩
  by_contra hcon
  have hstep : ∀ S : Finset (Fin n), ∃ S' : Finset (Fin n), CompDesign.IsStrictImprovement v B c S S' := by
    intro S
    by_contra hS
    push Not at hS
    exact hcon ⟨S, CompDesign.thm_4_1_terminal_is_pne v B c S hS⟩
  choose g hg using hstep
  refine hno ⟨fun t => g^[t] ∅, fun t => ?_⟩
  show CompDesign.IsStrictImprovement v B c (g^[t] ∅) (g^[t + 1] ∅)
  rw [Function.iterate_succ_apply']
  exact hg _
