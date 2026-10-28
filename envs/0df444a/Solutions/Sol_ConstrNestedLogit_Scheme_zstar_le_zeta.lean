-- Prove2me | solution 1 for ConstrNestedLogit.Scheme.zstar_le_zeta
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:19:02.392396+00:00
-- url     : https://prove2.me/submissions/8f44c5ba-ce3b-439f-a63e-cd5aebdf936a

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Scheme_Model

open ConstrNestedLogit.Scheme in
theorem solution {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ) (c : ι → ℝ)
    (i : ι) (q : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (Sstar : Finset (Fin n)) (hSfeas : ConstrNestedLogit.Space.spaceFeasible w c i Sstar)
    (hSopt : ∀ S, ConstrNestedLogit.Space.spaceFeasible w c i S → obj10 I i u S ≤ obj10 I i u Sstar)
    (hcard : q < Sstar.card)
    (Jstar : Finset (Fin n)) (hJsub : Jstar ⊆ Sstar) (hJcard : Jstar.card = q)
    (hJtop : ∀ j ∈ Jstar, ∀ k ∈ Sstar \ Jstar, ConstrNestedLogit.Space.utility I i u k ≤ ConstrNestedLogit.Space.utility I i u j) :
    feasible17 I w c i u Jstar (fun j => if j ∈ Sstar then 1 else 0) ∧
      ∀ x, optimal17 I w c i u Jstar x → obj10 I i u Sstar ≤ obj17 I i u x := by
  have hfeas : feasible17 I w c i u Jstar (fun j => if j ∈ Sstar then 1 else 0) := by
    refine ⟨fun j => ?_, ?_, fun j hj => ?_, fun k hk ⟨j, hj, hlt⟩ => ?_⟩
    · dsimp only; split_ifs <;> norm_num
    · have : (∑ j, w i j * (if j ∈ Sstar then (1 : ℝ) else 0)) = ∑ j ∈ Sstar, w i j := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [this]
      exact hSfeas
    · simp only [if_pos (hJsub hj)]
    · have hks : k ∉ Sstar := by
        intro hks
        have := hJtop j hj k (Finset.mem_sdiff.mpr ⟨hks, hk⟩)
        linarith
      simp only [if_neg hks]
  refine ⟨hfeas, fun x hx => ?_⟩
  have h := hx.2 _ hfeas
  have e : obj17 I i u (fun j => if j ∈ Sstar then 1 else 0) = obj10 I i u Sstar := by
    unfold obj17 obj10
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [← e]
  exact h
