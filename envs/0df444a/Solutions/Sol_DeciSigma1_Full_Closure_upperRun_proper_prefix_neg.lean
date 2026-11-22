-- Prove2me | solution 1 for DeciSigma1.Full.Closure.upperRun_proper_prefix_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:14:24.995652+00:00
-- url     : https://prove2.me/submissions/3226854f-82a5-4180-b942-7e286ca79c88

module
public import Mathlib.Data.Fintype.Powerset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Constraints
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Decide
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Theorems.Thm_DeciSigma1_Full_Closure_popRoot
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_forbiddenPredecessors
public import Theorems.Thm_DeciSigma1_Full_Closure_upperRun_nonempty_prefix
public import Theorems.Thm_DeciSigma1_Automata_derivedPairs_refl


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Automata
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
variable [Fintype V] [DecidableEq V]
variable (c : Fin n → Bool) (Γ : List (LitT n V))
variable {c Γ}
variable (c Γ)
variable {c Γ}
namespace DeciSigma1.Full.Closure
theorem _root_.solution {p : V × Bool} {γ : List (Fin n)} {i : ℕ}
    (h : (Automata.upperRun (signed c Γ) p γ).Nonempty) (hi : i < γ.length) :
    (Automata.upperRun (signed c Γ) p
        (γ.take i) ∩ forbiddenPredecessors c Γ).Nonempty := by
  have hnext := upperRun_nonempty_prefix (List.take_prefix (i + 1) γ) h
  rw [List.take_succ_eq_append_getElem hi] at hnext
  obtain ⟨r, hr, hn⟩ := popRoot hnext
  exact ⟨r, Finset.mem_inter.mpr ⟨hr,
    mem_forbiddenPredecessors.mpr ⟨(r.1, r.2, []), hn, Automata.derivedPairs_refl _ _⟩⟩⟩
end DeciSigma1.Full.Closure
