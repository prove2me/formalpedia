-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:49:13.321851+00:00
-- url     : https://prove2.me/submissions/822f421d-d770-4714-b828-02e18b6ce979

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity

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
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {UU : Set (Mat k r)} (hUU : UU ⊆ GV k r) {f : Mat k r → E} (hf : CkOn 0 UU f) :
    ContinuousOn f UU := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g hg
  have h1 : ContinuousAt f' g := hc.continuousOn.continuousAt (hU.mem_nhds hgU)
  apply (h1.continuousWithinAt (s := UU)).congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with y hyU hyUU
    exact he y hyU (hUU hyUU)
  · exact he g hgU (hUU hg)
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
