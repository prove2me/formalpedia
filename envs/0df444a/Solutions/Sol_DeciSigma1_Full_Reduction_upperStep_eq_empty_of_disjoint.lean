-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.upperStep_eq_empty_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:13:09.379842+00:00
-- url     : https://prove2.me/submissions/4cae5047-969e-4c70-8286-aba7e18283c1

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Finite.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Theorems.Thm_DeciSigma1_Automata_derivedPairs_refl
public import Theorems.Thm_DeciSigma1_Automata_mem_upperStep
public import Theorems.Thm_DeciSigma1_Full_Closure_mem_forbiddenPredecessors
public import Theorems.Thm_DeciSigma1_Full_Closure_signed_upper_neg
attribute [local simp] DeciSigma1.Automata.mem_upperStep



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Full.Closure
open DeciSigma1.Constraints
variable {n : Nat} {V : Type} [Fintype V] [DecidableEq V]
variable {c : Fin n → Bool} {Γ : List (LitT n V)}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution (P : Finset (V × Bool)) (l : Fin n)
    (h : Disjoint P (forbiddenPredecessors c Γ)) :
    Automata.upperStep (signed c Γ) P l = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨r, hr, a, hl, _⟩ := Automata.mem_upperStep.mp hx
  exact Finset.disjoint_left.mp h hr
    (mem_forbiddenPredecessors.mpr ⟨(r.1, r.2, []), signed_upper_neg hl,
        Automata.derivedPairs_refl _ _⟩)
end DeciSigma1.Full.Reduction
