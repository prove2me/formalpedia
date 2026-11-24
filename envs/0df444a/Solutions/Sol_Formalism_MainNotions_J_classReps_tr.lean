-- Prove2me | solution 1 for Formalism.MainNotions.J.classReps_tr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:42.701474+00:00
-- url     : https://prove2.me/submissions/51aa715d-cfe6-4d59-8c4d-c37f90b176db

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLa
import Theorems.Thm_Formalism_MainNotions_J_tr_tr_symm
import Theorems.Thm_Formalism_MainNotions_J_gmap_cj
import Theorems.Thm_Formalism_MainNotions_J_isom_symm
import Theorems.Thm_Formalism_MainNotions_J_cj_mem_isom
import Theorems.Thm_Formalism_MainNotions_J_genus_tr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
namespace Formalism.MainNotions.J
theorem _root_.solution {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L s) :
    IsClassReps h' (latMap φ L) (s.map ⟨latMap φ, tr_injective φ⟩) := by
  constructor
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_map.1 hM
    exact genus_tr hφ (hs.1 N hN)
  · intro M hM
    have hM' : latMap φ.symm M ∈ genus h L := by
      have := genus_tr (isom_symm hφ) hM
      rwa [tr_symm_tr] at this
    obtain ⟨N, ⟨hN, g, hg, e⟩, huniq⟩ := hs.2 _ hM'
    refine ⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩
    · rw [gmap_cj, e, tr_tr_symm]
    · rintro N' ⟨hN', g', hg', e'⟩
      obtain ⟨N₀, hN₀, rfl⟩ := Finset.mem_map.1 hN'
      have : N₀ = N := by
        refine huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩
        have h2 := gmap_cj φ.symm g' (latMap φ N₀)
        rw [tr_symm_tr] at h2
        change gmap g' (latMap φ N₀) = M at e'
        rw [h2, e']
      rw [this]; rfl
end Formalism.MainNotions.J
