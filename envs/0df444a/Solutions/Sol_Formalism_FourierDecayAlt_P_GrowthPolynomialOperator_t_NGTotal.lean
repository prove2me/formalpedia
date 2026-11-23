-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_NGTotal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:34.34156+00:00
-- url     : https://prove2.me/submissions/992ff146-5daa-4616-bb57-33c9fd816890

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
open Formalism.FourierDecayAlt.PB
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : NGTotal := by
  intro hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X ε ε' dd hA hRO hCP hRB hRNG
  obtain ⟨-, -, hng⟩ := hPS τ Rw I H H₁ X hA hRO hCP
  have hsubN : X.big X.ngSet ⊆ X.big X.nzSet := by
    intro p hp
    have hp' : (p.1 ∈ X.ngSet ∧ p.2 ∈ X.ngSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2 := hp
    have h1 : p.1 ∈ X.nzSet := (show X.G p.1 ≠ 0 ∧ ¬ X.gener p.1 from hp'.1.1).1
    have h2 : p.2 ∈ X.nzSet := (show X.G p.2 ≠ 0 ∧ ¬ X.gener p.2 from hp'.1.2.1).1
    show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2
    exact ⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩
  obtain ⟨hmN, -⟩ := hSF τ Rw I H H₁ X hA _ _ hsubN
  obtain ⟨-, habsN⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.ngSet ⊆ X.big X.ngSet)
  have hRB' : X.pairAbs (X.big X.nzSet) ≤ ε * dd := hRB
  have hRNG' : X.pairSum (X.one X.ngSet) ≤ ε' * dd := hRNG
  have hPhiN : X.PhiEq X.ngSet ≤ (ε + ε') * dd := by
    rw [hng]
    have := le_abs_self (X.pairSum (X.big X.ngSet))
    linarith
  exact hPhiN
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
