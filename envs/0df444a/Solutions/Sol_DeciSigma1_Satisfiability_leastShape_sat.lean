-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:34:29.867644+00:00
-- url     : https://prove2.me/submissions/0aeb9614-9a6f-4313-8f56-b3af334deaad

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_eq_bot
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_eq_top
public import Theorems.Thm_DeciSigma1_Satisfiability_node_le_leastShape
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_le_node
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution (hn : ¬ LabelClash Γ) : Covariant.Sat (leastShape Γ) Γ := by
  intro l hl
  cases l with
  | le x y => exact leastShape_mono (.lit hl)
  | leF x b => exact leastShape_le_node hl
  | fLe a x => exact node_le_leastShape hl
  | eqBot x => exact leastShape_eq_bot hn hl
  | eqTop x => exact leastShape_eq_top hn hl
end DeciSigma1.Satisfiability
