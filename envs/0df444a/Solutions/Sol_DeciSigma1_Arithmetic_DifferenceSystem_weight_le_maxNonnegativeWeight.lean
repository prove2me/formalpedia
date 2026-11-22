-- Prove2me | solution 1 for DeciSigma1.Arithmetic.DifferenceSystem.weight_le_maxNonnegativeWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:34.637738+00:00
-- url     : https://prove2.me/submissions/4e374e59-7f8b-465e-85ef-82f845555731

module
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_isWalk_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_le_maxNonnegativeWeight
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
open DeciSigma1.Arithmetic.DifferenceSystem
variable {ι : Type} (D : DifferenceSystem ι)
variable {D}
namespace DeciSigma1.Arithmetic.DifferenceSystem
theorem _root_.solution [Fintype ι] :
    ∀ p : List ι, D.IsWalk p → D.weight p ≤ (p.length - 1 : ℕ) * (D.maxNonnegativeWeight : ℤ)
  | [], _ => by simp
  | [_], _ => by simp
  | i :: j :: p, hw => by
    rw [isWalk_cons_cons] at hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hw.1
    have h1 := le_maxNonnegativeWeight hc
    have h2 := solution (j :: p) hw.2
    rw [weight_cons_cons, hc, Option.getD_some]
    simp only [List.length_cons, Nat.add_sub_cancel] at h2 ⊢
    push_cast at h2 ⊢
    nlinarith
end DeciSigma1.Arithmetic.DifferenceSystem
