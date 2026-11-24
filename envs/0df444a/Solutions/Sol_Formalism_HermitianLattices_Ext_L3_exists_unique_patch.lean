-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.exists_unique_patch
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:47.054413+00:00
-- url     : https://prove2.me/submissions/8e33e883-9f8e-4c71-982c-9aa6ab32ea0e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_patch
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (T : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hT : ∀ 𝔭 ∈ s, locF 𝔭.1 (T 𝔭) = T 𝔭 ∧ ∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧
      locF 𝔭.1 A = T 𝔭) :
    ∃! Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ (∀ 𝔭 ∈ s, locF 𝔭.1 Λ = T 𝔭) ∧
      ∀ 𝔭 ∉ s, locF 𝔭.1 Λ = locF 𝔭.1 L₀ := by
  classical
  let B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V := fun 𝔭 =>
    if h : 𝔭 ∈ s then (hT 𝔭 h).2.choose else L₀
  have hB1 : ∀ 𝔭 (h : 𝔭 ∈ s), Submodule.IsLattice K (B 𝔭) ∧ locF 𝔭.1 (B 𝔭) = T 𝔭 := by
    intro 𝔭 h
    simp only [B, dif_pos h]
    exact (hT 𝔭 h).2.choose_spec
  have hB2 : ∀ 𝔭 ∉ s, B 𝔭 = L₀ := by
    intro 𝔭 h
    simp only [B, dif_neg h]
  have hB : ∀ 𝔭, Submodule.IsLattice K (B 𝔭) := by
    intro 𝔭
    by_cases h : 𝔭 ∈ s
    · exact (hB1 𝔭 h).1
    · rw [hB2 𝔭 h]
      exact hL₀
  obtain ⟨hlat, hloc⟩ := LocF.patch hL₀ s B hB hB2
  refine ⟨_, ⟨hlat, fun 𝔭 h => (hloc 𝔭).trans (hB1 𝔭 h).2,
    fun 𝔭 h => (hloc 𝔭).trans (by rw [hB2 𝔭 h])⟩, ?_⟩
  rintro Λ ⟨-, h1, h2⟩
  rw [← LocF.iInf_locF (F := F) Λ]
  congr 1
  funext 𝔭
  by_cases h : 𝔭 ∈ s
  · rw [h1 𝔭 h, (hB1 𝔭 h).2]
  · rw [h2 𝔭 h, hB2 𝔭 h]
end Formalism.HermitianLattices.Ext.L3
