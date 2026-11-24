-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lgraded_rowGen_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:55.494367+00:00
-- url     : https://prove2.me/submissions/f37c91cd-a542-487a-9371-1c067f1e11d2

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℚ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  obtain ⟨b, j⟩ := v
  simp only [rowGen, aeval_X, lgraded_wa]
  by_cases h : b = a
  · subst h
    rw [if_pos rfl, if_pos rfl, pow_one]
    ring
  · simp [h]
end Formalism.GradedWeylDivisibility
