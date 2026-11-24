-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.adjugate_adjugate_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:05.186126+00:00
-- url     : https://prove2.me/submissions/b1c865ad-5c07-418e-a136-d58aed808ff0

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
theorem _root_.solution {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) :
    A.det • A.adjugate.adjugate = A.det ^ (Fintype.card n - 1) • A := by
  have h1 : A * (A.adjugate * A.adjugate.adjugate) = A.det ^ (Fintype.card n - 1) • A := by
    rw [Matrix.mul_adjugate, Matrix.det_adjugate, Matrix.mul_smul, Matrix.mul_one]
  rw [← h1, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
end Formalism.CohomologicalDescent.LD
