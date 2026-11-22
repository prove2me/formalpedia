-- Prove2me | solution 1 for Formalism.D5.Bal.chC_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:52:52.188936+00:00
-- url     : https://prove2.me/submissions/75545a33-ab06-4c1c-ba8e-6694e7b5540c

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_chC_mul_self

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
theorem _root_.solution (Hs : CycHost H) (g : E0 × H) : Hs.chC g * Hs.chC g = 1 := by
  rw [← AddChar.mul_apply, chC_mul_self, AddChar.zero_apply]
end Formalism.D5.Bal
