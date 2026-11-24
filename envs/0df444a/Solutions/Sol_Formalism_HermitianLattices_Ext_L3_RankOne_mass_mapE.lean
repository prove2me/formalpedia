-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.mass_mapE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:12.720509+00:00
-- url     : https://prove2.me/submissions/c4d78ebd-323a-4ba3-b8d7-2d5df69c7573

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mass_transfer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_mapE
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_conjE_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_gmap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_isLattice_mapE
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mapE_symm_mapE
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (φ : V ≃ₗ[K] V') {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    (hex : ∃ s, IsClassReps h L s) :
    (∃ s', IsClassReps h' (mapE φ L) s') ∧ mass h' (mapE φ L) = mass h L := by
  refine mass_transfer (mapE φ) (conjE φ) ?_ ?_ ?_ ?_ hex
  · intro g
    constructor
    · intro H x y
      have := H (φ x) (φ y)
      simpa [conjE_apply, hφ] using this
    · intro H x y
      obtain ⟨x, rfl⟩ := φ.surjective x
      obtain ⟨y, rfl⟩ := φ.surjective y
      simp only [conjE_apply, LinearEquiv.symm_apply_apply, hφ]
      exact H x y
  · intro g M
    ext y
    rw [mem_mapE, mem_gmap, mem_gmap, mem_mapE]
    have e : (conjE φ g).symm y = φ (g.symm (φ.symm y)) := rfl
    rw [e, LinearEquiv.symm_apply_apply]
  · intro p _ M
    ext y
    rw [mem_mapE]
    change (∃ s ∈ hcompl (K := K) p, s • φ.symm y ∈ M) ↔ (∃ s ∈ hcompl (K := K) p, s • y ∈ mapE φ M)
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [mem_mapE]
    have : φ.symm (s • y) = s • φ.symm y := (φ.symm.restrictScalars (𝓞 K)).map_smul s y
    rw [this]
  · intro M
    refine ⟨fun H => ?_, isLattice_mapE φ⟩
    have := isLattice_mapE φ.symm H
    rwa [mapE_symm_mapE] at this
end Formalism.HermitianLattices.Ext.L3.RankOne
