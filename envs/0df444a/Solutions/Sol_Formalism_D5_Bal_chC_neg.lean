-- Prove2me | solution 1 for Formalism.D5.Bal.chC_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:41.639799+00:00
-- url     : https://prove2.me/submissions/d182184e-5ffc-4d49-bcf9-5111c028f1fe

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
theorem _root_.solution (Hs : CycHost H) (g : E0 × H) : Hs.chC (-g) = Hs.chC g := by
  rw [Hs.7, Hs.7]
  have h : (-g).1.1 = g.1.1 := by
    show -g.1.1 = g.1.1
    generalize g.1.1 = e
    revert e
    decide
  rw [h]
end Formalism.D5.Bal
