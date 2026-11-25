-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.prod_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:50.010313+00:00
-- url     : https://prove2.me/submissions/488924ff-54c3-4cd5-afab-f6fb7e0868a2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.M
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (a b : ℕ → ℝ) (n : ℕ) (ha : ∀ i j, 1 ≤ i → i < j → j ≤ n → a j < a i)
    (hb : ∀ i j, 1 ≤ i → i < j → j ≤ n → b j < b i)
    (h : ∀ Y : ℂ, ∏ i ∈ Finset.Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Finset.Icc 1 n, (Y + (b i : ℂ))) :
    ∀ j ∈ Finset.Icc 1 n, a j = b j := by
  have root : ∀ (a b : ℕ → ℝ), (∀ Y : ℂ, ∏ i ∈ Finset.Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Finset.Icc 1 n, (Y + (b i : ℂ))) →
      ∀ j ∈ Finset.Icc 1 n, ∃ m ∈ Finset.Icc 1 n, b m = a j := by
    intro a b h j hj
    have h0 : ∏ i ∈ Finset.Icc 1 n, (-(a j : ℂ) + (a i : ℂ)) = 0 :=
      Finset.prod_eq_zero hj (by ring)
    rw [h] at h0
    obtain ⟨m, hm, hm0⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨m, hm, ?_⟩
    have : (b m : ℂ) = (a j : ℂ) := by linear_combination hm0
    exact_mod_cast this
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hj' := Finset.mem_Icc.1 hj
    obtain ⟨m, hm, hbm⟩ := root a b h j hj
    obtain ⟨m', hm', ham'⟩ := root b a (fun Y => (h Y).symm) j hj
    have hm1 := Finset.mem_Icc.1 hm
    have hm1' := Finset.mem_Icc.1 hm'
    have h1 : a j ≤ b j := by
      rcases lt_trichotomy m j with hlt | heq | hgt
      · exfalso
        have := ih m hlt hm
        have h2 := ha m j hm1.1 hlt hj'.2
        linarith
      · rw [← hbm, heq]
      · have := hb j m hj'.1 hgt hm1.2
        linarith
    have h2 : b j ≤ a j := by
      rcases lt_trichotomy m' j with hlt | heq | hgt
      · exfalso
        have := ih m' hlt hm'
        have h2 := hb m' j hm1'.1 hlt hj'.2
        linarith
      · rw [← ham', heq]
      · have := ha j m' hj'.1 hgt hm1'.2
        linarith
    exact le_antisymm h1 h2
end Formalism.FourierDecayAlt.P.Qx8
