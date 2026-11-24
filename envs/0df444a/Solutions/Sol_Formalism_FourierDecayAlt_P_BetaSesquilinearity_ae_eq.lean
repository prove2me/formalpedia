-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:32:11.309167+00:00
-- url     : https://prove2.me/submissions/b600c6dc-9062-482a-b3da-3355add34a08

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hAe : AeFromTests) (hRB : RegBound D A) (hRA : RegAverage D A) (hU : Unfold D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ᵐ τ ∂(volume.restrict Quad), normSqTau D τ F ≠ ∞ ∧
      (((normSqTau D τ F).toReal : ℝ) : ℂ) = betaInfTau D τ F F := by
  obtain ⟨hm, hu⟩ := hU F hF
  refine hAe _ _ hm (hRB.2.1 F F hF hF) ?_
  intro w₁ w₂ h1 h2 p1 p2
  obtain ⟨a, b⟩ := hu w₁ w₂ h1 h2 p1 p2
  exact ⟨a, b.trans (hRA F F hF hF w₁ w₂ h1 h2).2.symm⟩
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
