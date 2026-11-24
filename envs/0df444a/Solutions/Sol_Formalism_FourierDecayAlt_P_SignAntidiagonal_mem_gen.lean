-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.mem_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:18:37.075207+00:00
-- url     : https://prove2.me/submissions/75f7245f-3cc3-4d22-8e8f-104abcee4f3b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ}
    {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} {p q : Fin (2 * r + k + 1)} (h : InNp k r p q) :
    E p q - algebraMap ℂ A (dpsiP k r z' p q) ∈ Ideal.span (rgen k r z' E) := Ideal.subset_span ⟨p, q, h, rfl⟩
end Formalism.FourierDecayAlt.P.SignAntidiagonal
