-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_FourParts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.63691+00:00
-- url     : https://prove2.me/submissions/82247158-b938-4c84-bbb3-2ee8f26d2c48

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : FourParts := by
  intro τ Rw I H H₁ _ _ _ _ _ X hX
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext t
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases h1 : X.isId t
    · exact Or.inl (Or.inl (Or.inl h1))
    · by_cases h2 : X.G t = 0
      · exact Or.inl (Or.inl (Or.inr ⟨h2, h1⟩))
      · by_cases h3 : X.gener t
        · exact Or.inr ⟨h2, h3⟩
        · exact Or.inl (Or.inr ⟨h2, h3⟩)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t = 0 ∧ ¬ X.isId t := h2
    exact b.2 a
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t ≠ 0 ∧ ¬ X.gener t := h2
    exact b.1 (hX t a)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.isId t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact b.1 (hX t a)
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t = 0 ∧ ¬ X.isId t := h1
    have b : X.G t ≠ 0 ∧ ¬ X.gener t := h2
    exact b.1 a.1
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t = 0 ∧ ¬ X.isId t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact b.1 a.1
  · rw [Set.disjoint_left]
    intro t h1 h2
    have a : X.G t ≠ 0 ∧ ¬ X.gener t := h1
    have b : X.G t ≠ 0 ∧ X.gener t := h2
    exact a.2 b.2
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
