-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:48.934353+00:00
-- url     : https://prove2.me/submissions/3e13e2d5-1565-4dd1-abb7-e4986002f461

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_star_inv_eq_neg

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
theorem _root_.solution {J : Ideal A} (hJ : ∀ a ∈ J, star a ∈ J) {θ e : A}
    (he : (θ - star θ) * e = 1) : (trH r J).range = hermSub r J := by
  ext S
  rw [AddMonoidHom.mem_range, mem_hermSub]
  constructor
  · rintro ⟨Y, rfl⟩
    have hY := mem_entSub.mp Y.2
    refine ⟨?_, fun i j => ?_⟩
    · show (Y.1 + Y.1ᴴ)ᴴ = Y.1 + Y.1ᴴ
      rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
    · show (Y.1 + Y.1ᴴ) i j ∈ J
      rw [Matrix.add_apply, Matrix.conjTranspose_apply]
      exact J.add_mem (hY i j) (hJ _ (hY j i))
  · rintro ⟨hS, hSJ⟩
    have hse := star_inv_eq_neg he
    have hS' : ∀ i j, star (S j i) = S i j := fun i j => by rw [← Matrix.conjTranspose_apply, hS]
    refine ⟨⟨(θ * e) • S, mem_entSub.mpr fun i j => ?_⟩, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact J.mul_mem_left _ (hSJ i j)
    · show (θ * e) • S + ((θ * e) • S)ᴴ = S
      ext i j
      rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        star_mul', hS', star_mul', hse]
      linear_combination (S i j) * he
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
