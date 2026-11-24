-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Cell.map_skew
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:42.948524+00:00
-- url     : https://prove2.me/submissions/45e169d5-2839-4244-88db-965ea60affe2

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
theorem _root_.solution (ρ : A →+* C) (μ : C →+ A) (hμs : ∀ y, μ (star y) = star (μ y))
    (hμm : ∀ a y, μ (ρ a * y) = a * μ y) (H : Matrix κ κ A) (Y : Matrix κ κ C) :
    (H.map ρ * Y + Yᴴ * H.map ρ).map μ = H * Y.map μ + (Y.map μ)ᴴ * H := by
  ext i l
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, hμm,
    conjTranspose_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, hμm, hμs, mul_comm]
end Formalism.HermitianLattices.Ext.L3.HU.Cell
