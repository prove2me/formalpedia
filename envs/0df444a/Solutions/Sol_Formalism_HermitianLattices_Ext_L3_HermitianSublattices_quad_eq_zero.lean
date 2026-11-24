-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.quad_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:47.516933+00:00
-- url     : https://prove2.me/submissions/54cb2e4a-2bbf-4f5a-9f16-0e9bf18c0bb1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution {𝔟 : Ideal A} (h𝔟s : ∀ a ∈ 𝔟, star a ∈ 𝔟) (h𝔟2 : ∀ a ∈ 𝔟, ∀ b ∈ 𝔟, a * b = 0)
    (H : Matrix m m A) {Y : Matrix m r A} (hY : Y ∈ entSub m r 𝔟) : Yᴴ * H * Y = 0 := by
  have hY' := mem_entSub.mp hY
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.conjTranspose_apply, mul_comm (star _) (H k l), mul_assoc,
    h𝔟2 _ (h𝔟s _ (hY' k i)) _ (hY' l j), mul_zero]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
