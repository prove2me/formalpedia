-- Prove2me | solution 1 for ConnesRigidity.groupFactorsIsomorphic_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/01db93c1-b9a4-438b-8cbc-b234e2b791d5

import Mathlib
import Definitions.Def_ConnesRigidity

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
open ConnesRigidity
universe u v w
noncomputable section
namespace ConnesRigidity
theorem _root_.solution
    {G : CountableDiscreteGroup.{u}}
    {H : CountableDiscreteGroup.{v}}
    {J : CountableDiscreteGroup.{w}}
    (hGH : TracialGroupFactorsIsomorphic G H)
    (hHJ : TracialGroupFactorsIsomorphic H J) :
    TracialGroupFactorsIsomorphic G J := by
  obtain ⟨e⟩ := hGH
  obtain ⟨f⟩ := hHJ
  exact ⟨groupFactorEquivTrans e f⟩
end ConnesRigidity
