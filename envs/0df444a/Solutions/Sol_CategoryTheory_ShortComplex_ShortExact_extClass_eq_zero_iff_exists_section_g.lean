-- Prove2me | solution 1 for CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3c1ec44a-a1b8-5c50-afc0-2c4b9f274156

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g

set_option autoImplicit false

universe w v u
p2m_open "CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits"

theorem solution
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h0
    have hx : (Ext.mk₀ (𝟙 S.X₃)).comp hS.extClass (zero_add 1) = 0 := by
      rw [Ext.mk₀_id_comp, h0]
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) hx
    refine ⟨Ext.homEquiv₀ x₂, ?_⟩
    have : Ext.mk₀ (Ext.homEquiv₀ x₂ ≫ S.g) = Ext.mk₀ (𝟙 S.X₃) := by
      rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply, hx₂]
    exact Ext.homEquiv₀.symm.injective (by simpa [Ext.mk₀_homEquiv₀_apply] using this)
  · rintro ⟨s, hs⟩
    have h1 : (Ext.mk₀ s).comp ((Ext.mk₀ S.g).comp hS.extClass (zero_add 1)) (zero_add 1) = 0 := by
      rw [hS.comp_extClass, Ext.comp_zero]
    rwa [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs, Ext.mk₀_id_comp] at h1

end S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
end P2MW
export P2MW.S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g (solution)
