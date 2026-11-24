-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WCB.exists_cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:59:41.436719+00:00
-- url     : https://prove2.me/submissions/0b6aa32c-b824-4034-b2bf-ad39854a1da3

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_laurent_adjoin_eq_of_image_eq
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
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCB
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.HermitianLattices.Ext.L3.WCB
theorem _root_.solution [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
    (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V} (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l : K}
    (hl : l + star l = 1) :
    ∃ g : V ≃ₗ[K] V, g ∈ Formalism.HermitianLatticesTheory.isom h ∧ (∀ z, g (z - star l • Y z) = z + l • Y z) ∧
      (∀ z, ∃ z', z' - star l • Y z' = z) ∧ (∀ z, ∃ z', z' + l • Y z' = z) := by
  let S : V →ₗ[K] V := LinearMap.id - star l • Y
  let T : V →ₗ[K] V := LinearMap.id + l • Y
  have hS : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z - star l • Y z = 0 := hz
    exact laurent_adjoin_eq_of_image_eq han hY (star_star l) hl (sub_eq_zero.1 hz')
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have hz' : z + l • Y z = 0 := hz
    have hY' : ∀ a b, h ((-Y) a) b + h a ((-Y) b) = 0 := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg]
      linear_combination (-1 : K) * hY a b
    refine laurent_adjoin_eq_of_image_eq (l := star l) (m := l) han hY' rfl (by rw [add_comm]; exact hl) ?_
    rw [LinearMap.neg_apply, smul_neg]
    exact eq_neg_of_add_eq_zero_left hz'
  let eS := LinearEquiv.ofInjectiveEndo S hS
  let eT := LinearEquiv.ofInjectiveEndo T hT
  have heS : ∀ z, eS z = z - star l • Y z := fun z => rfl
  have heT : ∀ z, eT z = z + l • Y z := fun z => rfl
  refine ⟨eS.symm.trans eT, ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := eS.surjective x
    obtain ⟨b, rfl⟩ := eS.surjective y
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [heS, heS, heT, heT]
    simp only [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
    linear_combination (l + star l) * hY a b
  · intro z
    rw [← heS, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, heT]
  · intro z
    exact ⟨eS.symm z, by rw [← heS, LinearEquiv.apply_symm_apply]⟩
  · intro z
    exact ⟨eT.symm z, by rw [← heT, LinearEquiv.apply_symm_apply]⟩
end Formalism.HermitianLattices.Ext.L3.WCB
