-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.not_stalkIdeal_le_pow_succ_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:37:55.489535+00:00
-- url     : https://prove2.me/submissions/1d4408c5-e477-4f21-b2c4-0283e70472eb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisibility
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinatePolynomialRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_genericPoint_eq_maximalIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (D : X.IdealSheafData)
    (hloc : ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart p U n),
      restrictIdeal D U = ⊤ ∨ ∃ j : Fin n, restrictIdeal D U = c.coordIdeal {j})
    {C : Set X} (hC : IsIrreducible C) (hCsub : C ⊆ (D.support : Set X))
    (hCmax : ∀ C' : Set X, IsIrreducible C' → C ⊆ C' → C' ⊆ (D.support : Set X) → C' = C)
    (I : X.IdealSheafData) (a : ℕ) (ha : orderAt I hC.genericPoint = (a : ℕ∞)) :
    ¬ stalkIdeal I hC.genericPoint ≤ stalkIdeal D hC.genericPoint ^ (a + 1) := by
  intro hcon
  rw [stalkIdeal_genericPoint_eq_maximalIdeal p D hloc hC hCsub hCmax] at hcon
  have h : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt I hC.genericPoint :=
    (le_orderAt_iff I hC.genericPoint (a + 1)).mpr hcon
  rw [ha] at h
  have h2 : (a : ℕ∞) < ((a + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self a
  exact absurd h (not_le.mpr h2)
end FunctorialResolution.EmbeddedResolution
