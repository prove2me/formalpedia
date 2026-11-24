-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.semi_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.560205+00:00
-- url     : https://prove2.me/submissions/e7358e5f-34a9-406c-9471-f2296f08aad4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_nthElt_ge
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_nthElt_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n C : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {T : Fin C → Finset (Fin n)} (hT : SemiStd T) (a : ℕ) :
    Monotone fun c => nthElt (T c) a := by
  have step : ∀ c c' : Fin C, c.val + 1 = c'.val → nthElt (T c) a ≤ nthElt (T c') a := by
    intro c c' h
    by_cases ha : a < (T c').card
    · exact hT c c' h a ha
    · rw [nthElt_ge (not_lt.1 ha)]; exact nthElt_le _ _
  have all : ∀ d : ℕ, ∀ c c' : Fin C, c.val + d = c'.val → nthElt (T c) a ≤ nthElt (T c') a := by
    intro d
    induction d with
    | zero =>
      intro c c' h
      have : c = c' := Fin.ext (by omega)
      rw [this]
    | succ d ih =>
      intro c c' h
      have hlt : c.val + d < C := by have := c'.2; omega
      exact (ih c ⟨c.val + d, hlt⟩ rfl).trans (step ⟨c.val + d, hlt⟩ c' (by simp only; omega))
  intro c c' hcc
  have hle : c.val ≤ c'.val := hcc
  exact all (c'.val - c.val) c c' (by omega)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
