-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_against_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:48:09.849834+00:00
-- url     : https://prove2.me/submissions/f1e5ef72-89d5-4221-8318-dd96d71139b0

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n) (g : Gaussian n)
    (L₁ L₂ : List (Gaussian n)) :
    hinge_against c a g (L₁ ++ L₂) = hinge_against c a g L₁ + hinge_against c a g L₂ := by
  induction L₁ with
  | nil => simp [hinge_against]
  | cons h L ih => simp [hinge_against, ih, add_assoc]
end CSeparatedNPComplete
