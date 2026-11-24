-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.rho_antitone_of_interlacing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:10.587911+00:00
-- url     : https://prove2.me/submissions/44bce0f5-83ff-474b-831e-1ba44d5e1a98

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RhoAntitoneOfInterlacing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {k : ℕ} {u u' ρ : ℕ → ℝ} (h : I.Interlaces k u u' ρ) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k - 1 → ρ j ≤ ρ i := by
  intro i j hi hij hj
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ n hin ih =>
    have h1 := h n (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h2 := h (n + 1) (by simp only [Finset.mem_Icc, Set.mem_Icc]; omega)
    have h3 := ih (by omega)
    linarith [h1.2.2.1, h2.1]
end Formalism.FourierDecayAlt.P
