-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.generator_diag_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:24:51.582817+00:00
-- url     : https://prove2.me/submissions/40fbbee5-fb87-4be5-bab1-057599e84ea4

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a : Fin r) (v : Fin r × Fin r) :
    rowGen ℤ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := r) a v) := by
  rw [rowGen, aeval_X]
  unfold lgraded_wa
  split_ifs with h
  · obtain ⟨b, s⟩ := v
    simp only at h
    subst h
    ring
  · simp
end Formalism.CohomologicalDescent.LD
