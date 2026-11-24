-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.generator_diag_constant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:13.582881+00:00
-- url     : https://prove2.me/submissions/b29390c6-7bcd-4ab0-be50-1eee785d15ed

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a : Fin r) (c : ℤ) :
    rowGen ℤ a a (C c : MvPolynomial (Fin r × Fin r) ℤ) = Polynomial.C (C c) := by
  rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
end Formalism.CohomologicalDescent.LD
