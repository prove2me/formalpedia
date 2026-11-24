-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.RankOne.mass_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:01:25.668802+00:00
-- url     : https://prove2.me/submissions/252a72e9-4c0a-4b90-895d-47f31efe826f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic_mass_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic_sum_cast
import Theorems.Thm_Formalism_ThetaLiftIndependence_latLiftIndep


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
namespace Formalism.HermitianLattices.Ext.L3.RankOne
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  have hex : ∃ s, IsClassReps h L s := ⟨s, hs⟩
  rw [massBasic_mass_eq h L hex]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
end Formalism.HermitianLattices.Ext.L3.RankOne
