-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.sdec_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:32:21.582961+00:00
-- url     : https://prove2.me/submissions/7bd376b7-896a-42d1-8a81-d6ab8cedc359

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {n : ℕ} {ν : Fin n → ℂ} (h : ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)) :
    SDec fun k => ν k - ((k : ℕ) : ℂ) := by
  intro a b hab
  obtain ⟨N, hN⟩ := h a b hab
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (Fin.lt_def.1 hab)
  refine ⟨N + d, ?_⟩
  have h1 : ν a = ν b + N := by rw [← hN]; ring
  show ν a - ((a : ℕ) : ℂ) - (ν b - ((b : ℕ) : ℂ)) = _
  rw [hd, h1]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
