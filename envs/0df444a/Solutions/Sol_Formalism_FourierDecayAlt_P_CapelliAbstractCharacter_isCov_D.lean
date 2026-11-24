-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliAbstractCharacter.isCov_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:30.00833+00:00
-- url     : https://prove2.me/submissions/3560fc4c-88ad-4514-b5f4-20eed1235949

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliAbstractCharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
namespace Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
theorem _root_.solution (hE : GlRel E) {η : Fin n → A} (h : IsCov E η) : IsCov E (fun j => ∑ l, E j l * η l) := by
  intro a b c
  have key : ∀ l, E a b * (E c l * η l) - E c l * η l * E a b =
      (E a b * E c l - E c l * E a b) * η l + E c l * (E a b * η l - η l * E a b) := by
    intro l; noncomm_ring
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [key, hE a b c, h a b]
  by_cases hbc : b = c
  · subst hbc
    simp [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  · simp [hbc, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
end Formalism.FourierDecayAlt.P.CapelliAbstractCharacter
