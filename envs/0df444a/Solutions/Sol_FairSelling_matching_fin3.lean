-- Prove2me | solution 1 for FairSelling.matching_fin3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:48.315436+00:00
-- url     : https://prove2.me/submissions/a35fe1dd-7fef-494a-afb3-b89889bde752

import Mathlib
import Definitions.Def_RequestProject_Matching

set_option autoImplicit true
open FairSelling
set_option maxRecDepth 4000
namespace FairSelling
theorem _root_.solution (acc : Fin 3 → Fin 3 → Bool) (pa : Fin 3)
    (hpa : ∀ k, acc pa k = true)
    (hnorej : ∀ j, ∃ k, acc j k = true) :
    (∃ σ : Equiv.Perm (Fin 3), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, acc pa k = true ∧ ∀ j, j ≠ pa → acc j k = false) := by
  revert acc pa
  decide
end FairSelling
