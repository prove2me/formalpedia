-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.frame_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:47.634603+00:00
-- url     : https://prove2.me/submissions/2ede160a-0c71-4910-bb93-9b408bef4ddd

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_idl_two_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_different_power_conj_stable
import Theorems.Thm_Formalism_FourierDecayAlt_P_twistedLatticeBetween


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (g : ℕ) (hg : 0 < g) (ν : ℤ) :
    DiscreteTopology (S6.frameLat E (S6.perLat E g ν 1) 1) ∧
    Submodule.span ℝ (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) = ⊤ := by
  have hA : S6.idl E g 1 ν ≠ 0 := idl_ne_zero g hg 1 ν
  have hB : S6.idl E g 2 ν ≠ 0 := idl_ne_zero g hg 2 ν
  obtain ⟨hBL, hLA⟩ := twistedLatticeBetween E (S6.idl E g 1 ν) (S6.idl E g 2 ν) 1 (idl_two_le_one g ν)
    (different_power_conj_stable E g 2 ν)
  have hmem : ∀ x, x ∈ S6.frameLat E (S6.perLat E g ν 1) 1 ↔
      ∃ t ∈ S6.perLat E g ν 1, mixedEmbedding E t = x := by
    intro x
    simp [S6.frameLat]
  constructor
  · have hsub : (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) ⊆
        (mixedEmbedding.idealLattice E (Units.mk0 _ hA) : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (hmem x).1 hx
      exact (mixedEmbedding.mem_idealLattice E _).2 ⟨t, hLA ht, rfl⟩
    exact DiscreteTopology.of_subset
      (inferInstanceAs (DiscreteTopology (mixedEmbedding.idealLattice E (Units.mk0 _ hA)))) hsub
  · have hsub : (mixedEmbedding.idealLattice E (Units.mk0 _ hB) : Set (mixedEmbedding.mixedSpace E)) ⊆
        (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := (mixedEmbedding.mem_idealLattice E _).1 hx
      exact (hmem _).2 ⟨t, hBL ht, rfl⟩
    classical
    have hr : Set.range (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)) ⊆
        (S6.frameLat E (S6.perLat E g ν 1) 1 : Set (mixedEmbedding.mixedSpace E)) := by
      intro x hx
      have hx' : x ∈ mixedEmbedding.idealLattice E (Units.mk0 _ hB) := by
        rw [← mixedEmbedding.span_idealLatticeBasis]
        exact Submodule.subset_span hx
      exact hsub hx'
    rw [eq_top_iff, ← (mixedEmbedding.fractionalIdealLatticeBasis E (Units.mk0 _ hB)).span_eq]
    exact Submodule.span_mono hr
end Formalism.FourierDecayAlt.P.Cx2
