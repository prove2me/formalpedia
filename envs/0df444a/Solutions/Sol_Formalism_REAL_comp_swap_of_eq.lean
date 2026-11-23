-- Prove2me | solution 1 for Formalism.REAL.comp_swap_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:08.953601+00:00
-- url     : https://prove2.me/submissions/6d193275-1899-4eb1-bc04-7fb09c33692f

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {α β : Type*} [DecidableEq α] (f : α → β) (p q : α) (h : f p = f q) :
    f ∘ Equiv.swap p q = f := by
  funext x
  rw [Function.comp_apply, Equiv.swap_apply_def]
  by_cases h1 : x = p
  · rw [if_pos h1, h1]; exact h.symm
  · rw [if_neg h1]
    by_cases h2 : x = q
    · rw [if_pos h2, h2]; exact h
    · rw [if_neg h2]
end Formalism.REAL
