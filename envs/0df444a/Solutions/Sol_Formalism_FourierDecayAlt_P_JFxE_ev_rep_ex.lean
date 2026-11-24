-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.ev_rep_ex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:52:10.637814+00:00
-- url     : https://prove2.me/submissions/cfb14b60-02ab-4a7d-a931-2f0e6c701a24

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_lsum_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
      ∀ f x, ev Eop a f x = (L.map fun p => p.1 • Fw Eop p.2 f x).sum := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L, hL, fun f x => ?_⟩
  simp only [ev, h, lsum_apply, List.nil_append, Pi.smul_apply, Phi]
end Formalism.FourierDecayAlt.P.JFxE
