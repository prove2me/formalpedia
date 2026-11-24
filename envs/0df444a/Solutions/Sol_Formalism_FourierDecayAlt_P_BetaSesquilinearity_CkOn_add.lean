-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:32:24.297954+00:00
-- url     : https://prove2.me/submissions/61f9f2f3-91d8-419a-ab48-ae06fc1b163f

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
theorem _root_.solution {m : ℕ∞} {UU : Set (Mat k r)} {f₁ f₂ : Mat k r → E} (h₁ : CkOn m UU f₁)
    (h₂ : CkOn m UU f₂) : CkOn m UU (fun g => f₁ g + f₂ g) := by
  intro g₀ hg₀
  obtain ⟨U₁, f₁', hU₁, hg₁, hc₁, he₁⟩ := h₁ g₀ hg₀
  obtain ⟨U₂, f₂', hU₂, hg₂, hc₂, he₂⟩ := h₂ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => f₁' g + f₂' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
    (hc₁.mono Set.inter_subset_left).add (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show f₁ g + f₂ g = f₁' g + f₂' g
  rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
