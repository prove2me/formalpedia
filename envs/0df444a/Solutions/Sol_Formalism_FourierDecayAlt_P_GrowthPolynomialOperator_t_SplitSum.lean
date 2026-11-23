-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_SplitSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:35.119835+00:00
-- url     : https://prove2.me/submissions/532c23c9-cbc7-4478-b2e4-ba81791bc12b

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
open Classical
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : SplitSum := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X hA hD
  have hA' : Summable (fun t => ‖X.op t‖) ∧ Summable (fun t => ‖X.vec t‖) ∧ 0 < X.Gam1 := hA
  have hs : Summable X.op := Summable.of_norm hA'.1
  have hsI : ∀ S : Set τ, Summable (S.indicator X.op) := fun S => hs.indicator S
  have hpt : ∀ t, X.op t = X.idSet.indicator X.op t + X.genSet.indicator X.op t +
      X.ngSet.indicator X.op t + X.degSet.indicator X.op t := by
    intro t
    by_cases h1 : X.isId t
    · have m1 : t ∈ X.idSet := h1
      have m2 : t ∉ X.genSet := fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 (hD t h1)
      have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 (hD t h1)
      have m4 : t ∉ X.degSet := fun h => (show X.G t = 0 ∧ ¬ X.isId t from h).2 h1
      simp [Set.indicator_apply, m1, m2, m3, m4]
    · by_cases h2 : X.G t = 0
      · have m1 : t ∉ X.idSet := h1
        have m2 : t ∉ X.genSet := fun h => (show X.G t ≠ 0 ∧ X.gener t from h).1 h2
        have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).1 h2
        have m4 : t ∈ X.degSet := ⟨h2, h1⟩
        simp [Set.indicator_apply, m1, m2, m3, m4]
      · by_cases h3 : X.gener t
        · have m1 : t ∉ X.idSet := h1
          have m2 : t ∈ X.genSet := ⟨h2, h3⟩
          have m3 : t ∉ X.ngSet := fun h => (show X.G t ≠ 0 ∧ ¬ X.gener t from h).2 h3
          have m4 : t ∉ X.degSet := fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1
          simp [Set.indicator_apply, m1, m2, m3, m4]
        · have m1 : t ∉ X.idSet := h1
          have m2 : t ∉ X.genSet := fun h => h3 (show X.G t ≠ 0 ∧ X.gener t from h).2
          have m3 : t ∈ X.ngSet := ⟨h2, h3⟩
          have m4 : t ∉ X.degSet := fun h => h2 (show X.G t = 0 ∧ ¬ X.isId t from h).1
          simp [Set.indicator_apply, m1, m2, m3, m4]
  show ∑' t, X.op t = (∑' t, X.idSet.indicator X.op t + ∑' t, X.genSet.indicator X.op t +
    ∑' t, X.ngSet.indicator X.op t) + ∑' t, X.degSet.indicator X.op t
  have e1 : ∑' t, X.op t = ∑' t, (X.idSet.indicator X.op t + X.genSet.indicator X.op t +
      X.ngSet.indicator X.op t + X.degSet.indicator X.op t) := tsum_congr hpt
  rw [e1]
  first
    | rw [Summable.tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _),
        Summable.tsum_add ((hsI _).add (hsI _)) (hsI _), Summable.tsum_add (hsI _) (hsI _)]
    | rw [tsum_add (((hsI _).add (hsI _)).add (hsI _)) (hsI _),
        tsum_add ((hsI _).add (hsI _)) (hsI _), tsum_add (hsI _) (hsI _)]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
