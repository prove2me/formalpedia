-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.mem_genus_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:12.458914+00:00
-- url     : https://prove2.me/submissions/e03eaf4c-6ed2-430e-ac36-84b7885546e8

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
  (Φ : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V') (τ : (V ≃ₗ[K] V) ≃ (V' ≃ₗ[K] V'))
  (hτ : ∀ g, τ g ∈ isom h' ↔ g ∈ isom h)
  (hg : ∀ g M, Φ (gmap g M) = gmap (τ g) (Φ M))
  (hloc : ∀ p : Ideal (𝓞 K), p.IsMaximal → ∀ M, Φ (loc (K := K) p M) = loc (K := K) p (Φ M))
  (hlat : ∀ M, Submodule.IsLattice K (Φ M) ↔ Submodule.IsLattice K M)
include hτ hg hloc hlat
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (L M : Submodule (𝓞 K) V) : Φ M ∈ genus h' (Φ L) ↔ M ∈ genus h L := by
  unfold genus SameGenus
  simp only [Set.mem_ofPred_eq, hlat]
  refine and_congr_right fun _ => forall₂_congr fun p hp => ?_
  constructor
  · rintro ⟨g', hg', e⟩
    obtain ⟨g, rfl⟩ := τ.surjective g'
    refine ⟨g, (hτ g).1 hg', Φ.injective ?_⟩
    rw [hg, hloc p hp, hloc p hp, e]
  · rintro ⟨g, hg₁, e⟩
    refine ⟨τ g, (hτ g).2 hg₁, ?_⟩
    rw [← hloc p hp, ← hg, e, hloc p hp]
end Formalism.HermitianLattices.Ext.L3.RankOne
