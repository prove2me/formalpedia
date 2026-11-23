-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairBoundAbstract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:26.161179+00:00
-- url     : https://prove2.me/submissions/65f85220-7d5b-4122-aa27-e218c79af674

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_t_TextClosing

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
theorem _root_.solution : PairBoundAbstract := by
  intro hPI hEI hPS hSF τ Rw I H H₁ _ _ _ _ _ _ X Pg A ε ε' dd hPg hdd hA hNX hGG hRO hCP hIZ
    hRB hRNS hRM hRNG
  obtain ⟨-, hgen, hng⟩ := hPS τ Rw I H H₁ X hA hRO hCP
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
  have hRNS' : X.pairAbs (X.nsc X.genSet) ≤ ε * dd := hRNS
  have hRM' : X.pairSum (X.sc X.genSet) ≤ A * dd := hRM
  have hsub : X.big X.genSet ⊆ X.big X.nzSet := by
    intro p hp
    have hp' : (p.1 ∈ X.genSet ∧ p.2 ∈ X.genSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2 := hp
    have h1 : p.1 ∈ X.nzSet := (show X.G p.1 ≠ 0 ∧ X.gener p.1 from hp'.1.1).1
    have h2 : p.2 ∈ X.nzSet := (show X.G p.2 ≠ 0 ∧ X.gener p.2 from hp'.1.2.1).1
    show (p.1 ∈ X.nzSet ∧ p.2 ∈ X.nzSet ∧ X.rowOf p.1 = X.rowOf p.2) ∧ 2 ≤ X.s0 p.1 p.2
    exact ⟨⟨h1, h2, hp'.1.2.2⟩, hp'.2⟩
  obtain ⟨hm, -⟩ := hSF τ Rw I H H₁ X hA _ _ hsub
  obtain ⟨-, habs1⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.big X.genSet ⊆ X.big X.genSet)
  obtain ⟨-, habs2⟩ := hSF τ Rw I H H₁ X hA _ _ (subset_rfl : X.nsc X.genSet ⊆ X.nsc X.genSet)
  have hPhiG : X.PhiEq X.genSet ≤ (A + 2 * ε) * dd := by
    rw [hgen]
    have := le_abs_self (X.pairSum (X.big X.genSet))
    have := le_abs_self (X.pairSum (X.nsc X.genSet))
    linarith
  have hx : ‖X.part X.genSet‖ ^ 2 ≤ (Pg * (A + 2 * ε)) * dd := by
    have := hPI hEI τ Rw I H H₁ X Pg X.genSet hNX.1 hGG
    calc _ ≤ Pg * X.PhiEq X.genSet := this
      _ ≤ Pg * ((A + 2 * ε) * dd) := mul_le_mul_of_nonneg_left hPhiG hPg
      _ = _ := by ring
  have hy : ‖X.part X.ngSet‖ ^ 2 ≤ (Pg * (ε + ε')) * dd := by
    have := hPI hEI τ Rw I H H₁ X Pg X.ngSet hNX.2 hGG
    calc _ ≤ Pg * X.PhiEq X.ngSet := this
      _ ≤ Pg * ((ε + ε') * dd) := mul_le_mul_of_nonneg_left hPhiN hPg
      _ = _ := by ring
  have hIZ' : X.part X.idSet = 0 := hIZ
  show ‖X.part X.idSet + X.part X.genSet + X.part X.ngSet‖ ^ 2 ≤ _
  rw [hIZ', zero_add]
  have e : 1 + (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) + Pg * (ε + ε') = Pg * (A + 2 * ε) := by ring
  have hTC := t_TextClosing H (X.part X.genSet) (X.part X.ngSet)
    (Pg * (A + 2 * ε) - 1 - Pg * (ε + ε')) (Pg * (ε + ε')) dd hdd (by rw [e]; exact hx) hy
  rw [e] at hTC
  exact hTC
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
