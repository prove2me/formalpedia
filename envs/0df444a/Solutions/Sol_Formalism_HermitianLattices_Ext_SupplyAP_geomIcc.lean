-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.geomIcc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.228446+00:00
-- url     : https://prove2.me/submissions/5c072b88-4d83-4b09-9785-b57d3d7ca440

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
open Finset
open scoped ComplexOrder
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (u : ℝ) (hu : u ≠ 1) (M : ℕ) :
    ∑ m ∈ Icc 1 M, u ^ m = (u - u ^ (M + 1)) / (1 - u) := by
  have h1 : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    field_simp
    ring
end Formalism.HermitianLattices.Ext.SupplyAP
