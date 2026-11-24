-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.adjointness_polynomially_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:25.300806+00:00
-- url     : https://prove2.me/submissions/21f5a1c8-5cf9-4ecd-a8bc-2123ae89c7e8

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.AssemblePoly := by
  intro hSC k r Wp Wq _ _ _ _ _ _ D A hA hCC hB3 Θ ε d hε hd hSm hCom hPoly F F' hF hF' hsF hsF'
  obtain ⟨hStab, hcl⟩ := hSC k r Wp Wq D A hA hCC
  obtain ⟨hs1, hs2, h1, h2, h3, h4, hIC⟩ := hcl Θ ε d hε hd hSm hPoly F F' hF hF' hsF hsF'
  have hCk : ∀ G : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) G →
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) G := by
    intro G hG
    obtain ⟨c, hc⟩ := hG
    unfold CCle at hc
    first
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2.1
    | exact hc.1.1
    | exact hc
  exact hB3 (GPos D) Θ hStab hSm hCom F F' (hCk F hF) (hCk F' hF') hs1 hs2 h1 h2 h3 h4 hIC
end Formalism.FourierDecayAlt.P
