-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.isUnimodular_of_ortho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:24.03452+00:00
-- url     : https://prove2.me/submissions/ab0faea6-6fdc-4939-9223-a79c728caf51

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_form_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_exists_coord
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StandardSymmetricSums_mem_lat_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_isIntegralLat_of_ortho
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {n : ℕ}
    (hL : Formalism.HermitianLatticesTheory.IsOrthoLattice h L n) : Formalism.HermitianLatticesTheory.IsUnimodular h L := by
  have hint := isIntegralLat_of_ortho hL
  obtain ⟨e, hli, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro x hx
    obtain ⟨c, rfl⟩ := exists_coord hsp x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars] at hx
    have hc : ∀ i, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c i := by
      intro i
      have := hx (e i) (Submodule.subset_span ⟨i, rfl⟩)
      rw [form_left he] at this
      exact Submodule.mem_one.1 this
    choose r hr using hc
    exact (mem_lat_iff _).2 ⟨r, by simp only [hr]⟩
  · intro x hx
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.coe_restrictScalars]
    exact fun y hy => hint y hy x hx
end Formalism.HermitianLattices.Ext.L3
