-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.card_autL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:47.035097+00:00
-- url     : https://prove2.me/submissions/275acb37-0f06-4594-b89a-c8d3d1edb15a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap

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
theorem _root_.solution (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (Φ M)) = Nat.card (autL h M) := by
  refine (Nat.card_congr (τ.subtypeEquiv fun g => ?_)).symm
  change (g ∈ isom h ∧ gmap g M = M) ↔ (τ g ∈ isom h' ∧ gmap (τ g) (Φ M) = Φ M)
  rw [hτ, ← hg, Φ.injective.eq_iff]
end Formalism.HermitianLattices.Ext.L3.RankOne
