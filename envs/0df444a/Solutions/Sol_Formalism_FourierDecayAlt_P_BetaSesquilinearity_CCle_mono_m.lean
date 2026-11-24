-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:59:09.876181+00:00
-- url     : https://prove2.me/submissions/75e624ee-2897-46c2-8ec1-71819b964d34

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono

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
theorem _root_.solution {A : ℝ} {m m' : ℕ} (h : m ≤ m') {F : Mat k r → E} {c : ℝ} (hF : CCle A m' F c) :
    CCle A m F c := by
  obtain ⟨hc, hb⟩ := hF
  exact ⟨sCkOn_mono (by exact_mod_cast h) hc, fun u v hu hv hl g hg => hb u v hu hv (hl.trans h) g hg⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
