-- Prove2me | solution 1 for Formalism.D5.Bal.chC_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:51.73954+00:00
-- url     : https://prove2.me/submissions/b6942e5a-9caa-47c1-b3e1-3fd389d03dfa

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution (Hs : CycHost H) : Hs.chC * Hs.chC = 0 := by
  refine AddChar.ext _ _ (fun g => ?_)
  rw [AddChar.mul_apply, AddChar.zero_apply, Hs.7, sgn2]
  split_ifs <;> norm_num
end Formalism.D5.Bal
