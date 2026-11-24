-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.sCkOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:27.670942+00:00
-- url     : https://prove2.me/submissions/701ad942-11cb-4b8f-934e-9a5a1cd6c95b

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
theorem _root_.solution {m m' : ℕ∞} (h : m ≤ m') {UU : Set (Mat k r)} {f : Mat k r → E} (hf : CkOn m' UU f) :
    CkOn m UU f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (WithTop.coe_le_coe.mpr h), he⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
