-- Prove2me | solution 1 for BalanceSpecification.wordCount_submultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:41.79493+00:00
-- url     : https://prove2.me/submissions/72546605-7622-4f0e-a0b5-06b67ecaf2a2

module
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Theorems.Thm_BalanceSpecification_language_factorial
public import Theorems.Thm_BalanceSpecification_wordCount_add_le


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A]
namespace BalanceSpecification
theorem _root_.solution (X : ShiftSpace A) :
    Submultiplicative (fun n => (wordCount (language X) n : ℝ)) := by
  intro m n
  change (wordCount (language X) (m + n) : ℝ) ≤
    (wordCount (language X) m : ℝ) * wordCount (language X) n
  exact_mod_cast wordCount_add_le (language_factorial X) m n
end BalanceSpecification
