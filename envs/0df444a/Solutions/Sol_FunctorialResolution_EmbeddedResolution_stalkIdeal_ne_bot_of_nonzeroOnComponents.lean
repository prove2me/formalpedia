-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_ne_bot_of_nonzeroOnComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:01:57.553027+00:00
-- url     : https://prove2.me/submissions/7022d9bd-99c1-4d9f-abaf-1aca2a2d6a8b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_affineOpens_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_support_iff_stalkIdeal_ne_top
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_nonzeroOnComponents_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_eq_map_germ


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
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : NonzeroOnComponents I) (x : X) : stalkIdeal I x ≠ ⊥ := by
  intro hbot
  rw [nonzeroOnComponents_iff] at hI
  refine hI (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x) ?_
  have hTirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hTcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hgen : closure {hTirr.genericPoint} = irreducibleComponent x :=
    hTirr.isGenericPoint_genericPoint hTcl
  have hspec : hTirr.genericPoint ⤳ x := by
    rw [specializes_iff_mem_closure, hgen]
    exact mem_irreducibleComponent
  obtain ⟨V, hxV⟩ := Scheme.exists_affineOpens_mem x
  have hetaV : hTirr.genericPoint ∈ (V : X.Opens) := hspec.mem_open (V : X.Opens).isOpen hxV
  have hmapeq : CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) hTirr.genericPoint hetaV)
      = (CommRingCat.Hom.hom (X.presheaf.stalkSpecializes hspec)).comp
        (CommRingCat.Hom.hom (X.presheaf.germ (V : X.Opens) x hxV)) := by
    rw [← CommRingCat.hom_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have hetabot : stalkIdeal I hTirr.genericPoint = ⊥ := by
    rw [stalkIdeal_eq_map_germ I hTirr.genericPoint V hetaV, hmapeq, ← Ideal.map_map,
      ← stalkIdeal_eq_map_germ I x V hxV, hbot, Ideal.map_bot]
  have hbt : (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) ≠ ⊤ := by
    intro h
    have h1 : (1 : ↑(X.presheaf.stalk hTirr.genericPoint)) ∈
        (⊥ : Ideal ↑(X.presheaf.stalk hTirr.genericPoint)) := by
      rw [h]; exact Submodule.mem_top
    rw [Ideal.mem_bot] at h1
    exact one_ne_zero h1
  have hmem : hTirr.genericPoint ∈ I.support :=
    (mem_support_iff_stalkIdeal_ne_top I _).mpr (by rw [hetabot]; exact hbt)
  calc irreducibleComponent x = closure {hTirr.genericPoint} := hgen.symm
    _ ⊆ closure ((I.support : Set ↥X)) :=
        closure_mono (Set.singleton_subset_iff.mpr hmem)
    _ = (I.support : Set ↥X) := I.support.isClosed.closure_eq
end FunctorialResolution.EmbeddedResolution
