-- Prove2me | solution 1 for ConnesRigidity.PaperAnalyticInput.gamma_not_isomorphic_lambda
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/c97a2e80-67de-4d16-8ec5-4c747d851ee2

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
open ConnesRigidity
open ConnesRigidity.PaperAnalyticInput
namespace ConnesRigidity.PaperAnalyticInput
theorem _root_.solution (n : ℕ) :
    ¬GroupsIsomorphic (gammaGroup n) lambdaGroup :=
  not_groupsIsomorphic_of_orderFour (gamma_has_order_four n)
    paperLambda_orderOf_ne_four
end ConnesRigidity.PaperAnalyticInput
