-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinE.form_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.114147+00:00
-- url     : https://prove2.me/submissions/82b83bd6-4fe8-4caa-887b-362d966a3d26

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinE
variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]
namespace Formalism.HermitianLattices.Ext.L3.PinE
theorem _root_.solution (H' X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * HH H' * fromBlocks 1 0 0 X' =
      fromBlocks 1 0 0 (X'ᴴ * H' * X') := by
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply]
end Formalism.HermitianLattices.Ext.L3.PinE
