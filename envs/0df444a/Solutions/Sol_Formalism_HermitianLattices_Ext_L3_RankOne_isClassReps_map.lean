-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.isClassReps_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:41.576573+00:00
-- url     : https://prove2.me/submissions/bbfcd21a-facd-4ee9-bb39-ac1db4d3942e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mem_genus_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsLattice K (Φ M) ↔ Submodule.IsLattice K M)
include hτ hg hloc hlat
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution {L : Submodule (𝓞 K) V} {s : Finset (Submodule (𝓞 K) V)}
    (hs : IsClassReps h L s) : IsClassReps h' (Φ L) (s.map Φ.toEmbedding) := by
  constructor
  · intro N hN
    obtain ⟨M, hM, rfl⟩ := Finset.mem_map.1 hN
    exact (mem_genus_iff Φ τ hτ hg hloc hlat L M).2 (hs.1 M hM)
  · intro N hN
    obtain ⟨M, rfl⟩ := Φ.surjective N
    obtain ⟨M₀, ⟨hM₀, g, hg₀, e⟩, huniq⟩ := hs.2 M ((mem_genus_iff Φ τ hτ hg hloc hlat L M).1 hN)
    refine ⟨Φ M₀, ⟨Finset.mem_map.2 ⟨M₀, hM₀, rfl⟩, τ g, (hτ g).2 hg₀, by rw [← hg, e]⟩, ?_⟩
    rintro N₁ ⟨hN₁, g', hg', e'⟩
    obtain ⟨M₁, hM₁, rfl⟩ := Finset.mem_map.1 hN₁
    obtain ⟨g₁, rfl⟩ := τ.surjective g'
    have : M₁ = M₀ := huniq M₁ ⟨hM₁, g₁, (hτ g₁).1 hg', Φ.injective (by rw [hg]; exact e')⟩
    rw [this]; rfl
end Formalism.HermitianLattices.Ext.L3.RankOne
