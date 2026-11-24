-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.exists_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:09.56899+00:00
-- url     : https://prove2.me/submissions/519b8af3-2c74-4fa1-93bf-2a2b7996ac26

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix

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
variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
theorem _root_.solution (B : AddSubgroup A) (Z' : AddSubgroup Z) (g : A → Z) (p : A → Prop)
    (hφ : ∀ a, p a → g a ∈ Z' → ∃ φ : B →+ Z, (∀ b : B, g (a + b) = g a + φ b) ∧
      ∀ z ∈ Z', ∃ b, φ b = z) (z : Z) (hz : z ∈ Z') :
    ∃ β : A → A, (∀ a, β a ∈ B) ∧ (∀ a, ∀ b ∈ B, β (a + b) = β a) ∧
      ∀ a, p a → g a ∈ Z' → g (a + β a) = g a + z ∧ g (a - β a) = g a - z := by
  classical
  have key : ∀ a', p a' → g a' ∈ Z' → ∀ φ : B →+ Z, (∀ b : B, g (a' + b) = g a' + φ b) →
      ∀ b0 : B, φ b0 = z → ∀ a : A, (a' : A ⧸ B) = a →
      g (a + b0) = g a + z ∧ g (a - b0) = g a - z := by
    intro a' _ _ φ hφ1 b0 hb0 a haa
    have hc : -a' + a ∈ B := QuotientAddGroup.eq.mp haa
    obtain ⟨c, hcdef⟩ : ∃ c : B, (c : A) = -a' + a := ⟨⟨_, hc⟩, rfl⟩
    have ha : a = a' + (c : A) := by rw [hcdef]; abel
    have hga : g a = g a' + φ c := by rw [← hφ1 c, ← ha]
    constructor
    · rw [show a + (b0 : A) = a' + ((c + b0 : B) : A) by rw [AddSubgroup.coe_add, ha]; abel,
        hφ1, map_add, hb0, hga, add_assoc]
    · rw [show a - (b0 : A) = a' + ((c - b0 : B) : A) by rw [AddSubgroup.coe_sub, ha]; abel,
        hφ1, map_sub, hb0, hga, add_sub_assoc]
  let good : A ⧸ B → Prop := fun x => ∃ a' : A, (a' : A ⧸ B) = x ∧ p a' ∧ g a' ∈ Z'
  let β' : A ⧸ B → A := fun x =>
    if h : good x then
      ((((hφ h.choose h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.2 z hz).choose : B) : A)
    else 0
  refine ⟨fun a => β' (a : A ⧸ B), fun a => ?_, fun a b hb => ?_, fun a hpa hga => ?_⟩
  · simp only [β']
    split_ifs
    · exact SetLike.coe_mem _
    · exact B.zero_mem
  · have hq : ((a + b : A) : A ⧸ B) = (a : A ⧸ B) := by
      rw [QuotientAddGroup.eq]
      have h' : -(a + b) + a = -b := by abel
      rw [h']
      exact B.neg_mem hb
    show β' _ = β' _
    rw [hq]
  · have h : good (a : A ⧸ B) := ⟨a, rfl, hpa, hga⟩
    simp only [β', dif_pos h]
    exact key _ h.choose_spec.2.1 h.choose_spec.2.2 _
      (hφ _ h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.1 _
      ((hφ _ h.choose_spec.2.1 h.choose_spec.2.2).choose_spec.2 z hz).choose_spec a
      h.choose_spec.1
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
