-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:07.759543+00:00
-- url     : https://prove2.me/submissions/d558c4ef-79a0-4cdf-9f43-f8bd0b4991d5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_exists_shift

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
theorem _root_.solution [Finite A] (B : AddSubgroup A) (Z' : AddSubgroup Z) (g : A → Z) (p : A → Prop)
    (hp : ∀ a, ∀ b ∈ B, (p (a + b) ↔ p a))
    (hφ : ∀ a, p a → g a ∈ Z' → ∃ φ : B →+ Z, (∀ b : B, g (a + b) = g a + φ b) ∧
      ∀ z ∈ Z', ∃ b, φ b = z) :
    Nat.card {a // p a ∧ g a ∈ Z'} = Nat.card {a // p a ∧ g a = 0} * Nat.card Z' := by
  classical
  have hβ : ∀ z : Z', ∃ β : A → A, (∀ a, β a ∈ B) ∧ (∀ a, ∀ b ∈ B, β (a + b) = β a) ∧
      ∀ a, p a → g a ∈ Z' → g (a + β a) = g a + z ∧ g (a - β a) = g a - z :=
    fun z => exists_shift B Z' g p hφ z z.2
  choose β hβB hβc hβg using hβ
  let e : {a // p a ∧ g a = 0} × Z' ≃ {a // p a ∧ g a ∈ Z'} :=
  { toFun := fun x => ⟨x.1.1 + β x.2 x.1.1, by
      obtain ⟨⟨a, hpa, hga⟩, z⟩ := x
      have h0 : g a ∈ Z' := hga ▸ Z'.zero_mem
      refine ⟨(hp a _ (hβB z a)).mpr hpa, ?_⟩
      rw [(hβg z a hpa h0).1, hga, zero_add]
      exact z.2⟩
    invFun := fun t => (⟨t.1 - β ⟨g t.1, t.2.2⟩ t.1, by
      obtain ⟨t, hpt, hgt⟩ := t
      refine ⟨?_, ?_⟩
      · rw [sub_eq_add_neg]
        exact (hp t _ (B.neg_mem (hβB _ t))).mpr hpt
      · rw [(hβg ⟨g t, hgt⟩ t hpt hgt).2]
        exact sub_self _⟩, ⟨g t.1, t.2.2⟩)
    left_inv := by
      rintro ⟨⟨a, hpa, hga⟩, z⟩
      have h0 : g a ∈ Z' := hga ▸ Z'.zero_mem
      have hg : g (a + β z a) = z := by rw [(hβg z a hpa h0).1, hga, zero_add]
      have hw : (⟨g (a + β z a), hg ▸ z.2⟩ : Z') = z := Subtype.ext hg
      refine Prod.ext (Subtype.ext ?_) hw
      show a + β z a - β ⟨g (a + β z a), _⟩ (a + β z a) = a
      rw [hw, hβc z a _ (hβB z a), add_sub_cancel_right]
    right_inv := by
      rintro ⟨t, hpt, hgt⟩
      apply Subtype.ext
      show t - β ⟨g t, hgt⟩ t + β ⟨g t, hgt⟩ (t - β ⟨g t, hgt⟩ t) = t
      rw [sub_eq_add_neg, hβc _ t _ (B.neg_mem (hβB _ t))]
      abel }
  rw [← Nat.card_congr e, Nat.card_prod]
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices
