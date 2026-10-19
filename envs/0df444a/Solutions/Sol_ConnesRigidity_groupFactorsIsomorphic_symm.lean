-- Prove2me | solution 1 for ConnesRigidity.groupFactorsIsomorphic_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/697e57d8-5493-4464-abfe-2a376fcc49ac

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
    (h : TracialGroupFactorsIsomorphic G H) :
    TracialGroupFactorsIsomorphic H G := by
  obtain ⟨e⟩ := h
  exact ⟨groupFactorEquivSymm e⟩
end ConnesRigidity
