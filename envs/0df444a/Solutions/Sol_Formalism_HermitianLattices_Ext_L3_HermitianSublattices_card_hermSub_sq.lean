-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:05.244964+00:00
-- url     : https://prove2.me/submissions/b3a2a5c2-630b-491e-af09-bd5a312375d5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_star_inv_eq_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_range_trH

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
    (he : (θ - star θ) * e = 1) : Nat.card (hermSub r J) ^ 2 = Nat.card (entSub r r J) := by
  classical
  have hse := star_inv_eq_neg he
  have hsu : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star, neg_sub]
  have hkerm : ∀ Y : (trH r J).ker, ∀ i j, star (Y.1.1 j i) = -(Y.1.1 i j) := by
    intro Y i j
    have h := congrFun (congrFun (AddMonoidHom.mem_ker.mp Y.2) i) j
    change (Y.1.1 + Y.1.1ᴴ) i j = (0 : Matrix r r A) i j at h
    rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at h
    linear_combination h
  let e1 : (trH r J).ker ≃ hermSub r J :=
  { toFun := fun Y => ⟨(θ - star θ) • Y.1.1, mem_hermSub.mpr ⟨by
        ext i j
        rw [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, star_mul', hsu,
          hkerm]
        ring, fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul]
        exact J.mul_mem_left _ (mem_entSub.mp Y.1.2 i j)⟩⟩
    invFun := fun S => ⟨⟨e • S.1, mem_entSub.mpr fun i j => by
        rw [Matrix.smul_apply, smul_eq_mul]
        exact J.mul_mem_left _ ((mem_hermSub.mp S.2).2 i j)⟩, by
        rw [AddMonoidHom.mem_ker]
        change e • S.1 + (e • S.1)ᴴ = 0
        have hS := (mem_hermSub.mp S.2).1
        have hS' : ∀ i j, star (S.1 j i) = S.1 i j := fun i j => by
          rw [← Matrix.conjTranspose_apply, hS]
        ext i j
        rw [Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
          star_mul', hS', hse, Matrix.zero_apply]
        ring⟩
    left_inv := fun Y => by
      apply Subtype.ext
      apply Subtype.ext
      change e • (θ - star θ) • Y.1.1 = Y.1.1
      rw [smul_smul, mul_comm, he, one_smul]
    right_inv := fun S => by
      apply Subtype.ext
      change (θ - star θ) • e • S.1 = S.1
      rw [smul_smul, he, one_smul] }
  have hq := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (trH r J).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (trH r J)).toEquiv,
    range_trH hJ he, Nat.card_congr e1] at hq
  rw [hq, sq]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
