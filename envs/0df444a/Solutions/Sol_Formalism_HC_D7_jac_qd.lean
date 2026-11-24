-- Prove2me | solution 1 for Formalism.HC.D7.jac_qd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:05:56.59442+00:00
-- url     : https://prove2.me/submissions/272b1161-7c79-4623-8823-dcab78833aca

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_q4
import Theorems.Thm_Formalism_HC_D7_d4
import Theorems.Thm_Formalism_HC_D7_jac_dq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution : jacobiSym (q : ℤ) d = 1 := by
  rw [jacobiSym.quadratic_reciprocity_three_mod_four (q4 hH) (d4 hH), jac_dq hH]
  norm_num
end Formalism.HC.D7
