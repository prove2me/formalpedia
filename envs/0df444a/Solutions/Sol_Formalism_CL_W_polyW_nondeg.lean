-- Prove2me | solution 1 for Formalism.CL.W.polyW_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:04.694836+00:00
-- url     : https://prove2.me/submissions/060a1cc0-c281-40ec-81ec-cd679a6857db

import Definitions.Def_Formalism_WachModuleLifts_StatementW
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CL Formalism.CL.W
open Polynomial
variable (p : ℕ) [Fact p.Prime]
namespace Formalism.CL.W
theorem _root_.solution : (polyW p).N ≠ ⊥ ∧ ¬ IsUnit (polyBase p).π₀ := by
  constructor
  · intro h
    have : (1 : K p) ∈ (polyW p).N := ⟨1, by simp⟩
    rw [h, Submodule.mem_bot] at this; exact one_ne_zero this
  · simp only [polyBase]; exact Polynomial.not_isUnit_X
end Formalism.CL.W
