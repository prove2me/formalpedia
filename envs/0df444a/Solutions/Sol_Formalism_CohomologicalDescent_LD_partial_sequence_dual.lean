-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.partial_sequence_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:19:07.453218+00:00
-- url     : https://prove2.me/submissions/edb5b353-1bdb-4af5-a1bc-ffdd9780b47c

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
theorem _root_.solution {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (t : ℕ) (ht : t < r) :
    partialSumOfExponents (dualWt M ν) t = M - partialSumOfExponents ν (r - (t + 1)) := by
  unfold partialSumOfExponents dualWt
  rw [dif_pos ht, dif_pos (by omega)]
  rfl
end Formalism.CohomologicalDescent.LD
