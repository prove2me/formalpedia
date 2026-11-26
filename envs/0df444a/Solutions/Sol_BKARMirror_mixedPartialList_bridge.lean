-- Prove2me | solution 1 for BKARMirror.mixedPartialList_bridge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:15:24.147802+00:00
-- url     : https://prove2.me/submissions/bfff64a8-2ee0-4355-b338-303d9f31f2e9

import Mathlib
import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace BKARMirror
theorem _root_.solution :
    ∀ (l : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      mixedPartialList l ρ = BKAR.mixedPartialList l ρ
  | [], _ρ => rfl
  | e :: es, ρ => by
      show partialDeriv e (mixedPartialList es ρ)
        = BKAR.partialDeriv e (BKAR.mixedPartialList es ρ)
      rw [solution es ρ]
      rfl
end BKARMirror
