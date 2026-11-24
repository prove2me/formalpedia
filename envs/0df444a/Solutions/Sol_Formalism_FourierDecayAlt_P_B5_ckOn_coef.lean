-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ckOn_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:00:50.279815+00:00
-- url     : https://prove2.me/submissions/10d427e6-a540-4571-91be-10546e0eec68

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {m : ℕ∞} {UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E)} {φ : Mat k r → E}
    (ha : CkOn ⊤ UU a) (hφ : CkOn m (GV k r) φ) (hs : closure {g | g ∈ GV k r ∧ φ g ≠ 0} ⊆ UU) :
    CkOn m (GV k r) (fun x => a x (φ x)) := by
  intro g₀ hg₀
  by_cases hc : g₀ ∈ closure {g | g ∈ GV k r ∧ φ g ≠ 0}
  · obtain ⟨U1, a', hU1, hg1, ha', he1⟩ := ha g₀ (hs hc)
    obtain ⟨U2, φ', hU2, hg2, hφ', he2⟩ := hφ g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => a' x (φ' x), hU1.inter hU2, ⟨hg1, hg2⟩, ?_, ?_⟩
    · have hR : ContDiffOn ℝ (m : WithTop ℕ∞)
          (fun x => ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ (a' x)) (U1 ∩ U2) :=
        (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).contDiff.comp_contDiffOn
          ((ha'.mono Set.inter_subset_left).of_le (by exact_mod_cast le_top))
      exact hR.clm_apply (hφ'.mono Set.inter_subset_right)
    · intro g hg hgG
      simp only [he1 g hg.1 hgG, he2 g hg.2 hgG]
  · refine ⟨(closure {g | g ∈ GV k r ∧ φ g ≠ 0})ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hc,
      contDiffOn_const, ?_⟩
    intro g hg hgG
    have hz : φ g = 0 := by
      by_contra hne
      exact hg (subset_closure ⟨hgG, hne⟩)
    simp [hz]
end Formalism.FourierDecayAlt.P.B5
