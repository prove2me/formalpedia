-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cell.expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:29.350848+00:00
-- url     : https://prove2.me/submissions/16e954ff-8a1d-4b04-9a2a-8f9a16c8eac1

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]
namespace Formalism.HermitianLattices.Ext.L3.HU.Cell
theorem _root_.solution {H X0 : Matrix κ κ A} (hX0 : X0ᴴ * H * X0 = H) (D : Matrix κ κ A) :
    (X0 * (1 + D))ᴴ * H * (X0 * (1 + D)) = H + (H * D + Dᴴ * H) + Dᴴ * H * D := by
  rw [conjTranspose_mul, conjTranspose_add, conjTranspose_one]
  calc _ = (1 + Dᴴ) * (X0ᴴ * H * X0) * (1 + D) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hX0]; noncomm_ring
end Formalism.HermitianLattices.Ext.L3.HU.Cell
