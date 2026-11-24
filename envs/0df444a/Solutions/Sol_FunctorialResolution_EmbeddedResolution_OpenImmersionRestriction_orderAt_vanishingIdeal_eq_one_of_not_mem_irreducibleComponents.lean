-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.orderAt_vanishingIdeal_eq_one_of_not_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:47.076639+00:00
-- url     : https://prove2.me/submissions/8343a32f-679c-4502-9cfc-f74879f20388

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealAssignment
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_VanishingIdealOrderOne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_maximalIdeal_stalk_ne_bot_of_specializes
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_orderAt_vanishingIdeal_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
theorem _root_.solution
    (X : Scheme.{u}) [IsLocallyNoetherian X] (S : Closeds ↥X) (x : ↥X)
    (hx : IsGenericPoint x (S : Set ↥X))
    (hS : (S : Set ↥X) ∉ irreducibleComponents ↥X) :
    FunctorialResolution.EmbeddedResolution.orderAt (Scheme.IdealSheafData.vanishingIdeal S) x = 1 := by
  have hx' : closure ({x} : Set ↥X) = (S : Set ↥X) := hx
  have hSirr : IsIrreducible (S : Set ↥X) := by
    rw [← hx']
    exact isIrreducible_singleton.closure
  have hxS : x ∈ (S : Set ↥X) := by
    rw [← hx']
    exact subset_closure (Set.mem_singleton x)
  have hMax : Maximal (fun s : Set ↥X => IsIrreducible s ∧ s ⊆ (S : Set ↥X)) (S : Set ↥X) := by
    constructor
    · exact ⟨hSirr, subset_rfl⟩
    · intro b hb _
      exact hb.2
  obtain ⟨t, htpre, hSt, hmaxt⟩ := exists_preirreducible (S : Set ↥X) hSirr.2
  have htirr : IsIrreducible t := ⟨⟨x, hSt hxS⟩, htpre⟩
  have htclosed : IsClosed t := by
    have h1 : closure t = t := hmaxt (closure t) htpre.closure subset_closure
    rw [← h1]
    exact isClosed_closure
  have htmem : t ∈ irreducibleComponents ↥X := by
    constructor
    · exact htirr
    · intro u hu htu
      exact (hmaxt u hu.2 htu).le
  have hSnet : (S : Set ↥X) ≠ t := by
    intro hEq
    exact hS (hEq ▸ htmem)
  obtain ⟨y, hy⟩ := QuasiSober.sober htirr htclosed
  have hy' : closure ({y} : Set ↥X) = t := hy
  have hyx : y ⤳ x := by
    rw [specializes_iff_mem_closure, hy']
    exact hSt hxS
  have hyne : y ≠ x := by
    intro hEq
    apply hSnet
    rw [← hx', ← hEq]
    exact hy'
  have hbot : IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x) ≠ ⊥ :=
    maximalIdeal_stalk_ne_bot_of_specializes X x y hyx hyne
  exact _root_.FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one S x (S : Set ↥X) hMax hx hbot
end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
