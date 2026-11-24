-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cell.quad_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:55.603746+00:00
-- url     : https://prove2.me/submissions/41f596f7-8e12-448c-8dc9-3ddd51409526

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
open Formalism.HermitianLattices.Ext.L3.HU.Cell
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A A' C : Type*} [CommRing A] [StarRing A] [CommRing A'] [CommRing C] [StarRing C]
namespace Formalism.HermitianLattices.Ext.L3.HU.Cell
theorem _root_.solution (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y)) (h2 : ∀ y z, μ y * μ z = 0)
    (H : Matrix κ κ A) (Y : Matrix κ κ C) : (Y.map μ)ᴴ * H * Y.map μ = 0 := by
  ext i l
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro m _
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hμs, mul_right_comm, h2, zero_mul]
end Formalism.HermitianLattices.Ext.L3.HU.Cell
