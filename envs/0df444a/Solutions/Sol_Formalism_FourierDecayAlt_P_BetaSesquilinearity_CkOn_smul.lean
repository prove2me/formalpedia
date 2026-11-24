-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:28:39.13911+00:00
-- url     : https://prove2.me/submissions/76c4aa16-b7ff-4906-a49c-dc70fcd03dcc

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
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution {m : ℕ∞} {UU : Set (Mat k r)} (c : ℂ) {f : Mat k r → E} (hf : CkOn m UU f) :
    CkOn m UU (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, he⟩ := hf g₀ hg₀
  exact ⟨U, fun g => c • f' g, hU, hgU, hc.const_smul c, fun g hg hgG => by
    show c • f g = c • f' g
    rw [he g hg hgG]⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
