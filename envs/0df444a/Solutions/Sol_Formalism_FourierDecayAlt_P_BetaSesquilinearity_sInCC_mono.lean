-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:43:32.688444+00:00
-- url     : https://prove2.me/submissions/cc1dd6a1-9941-4f37-8f77-58a54ba82a56

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_mono_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CCle_mono_A

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {A A' : ℝ} (h : A ≤ A') {m m' : ℕ} (hm : m ≤ m') {F : Mat k r → E} (hF : InCC A' m' F) :
    InCC A m F := by
  obtain ⟨c, hc⟩ := hF
  exact ⟨c, CCle_mono_A h (CCle_mono_m hm hc)⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
