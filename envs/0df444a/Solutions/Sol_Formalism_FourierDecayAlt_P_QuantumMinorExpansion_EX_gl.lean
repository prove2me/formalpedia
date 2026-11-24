-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.EX_gl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:47.865033+00:00
-- url     : https://prove2.me/submissions/aa6fb5c5-6697-4980-8202-e94537892208

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution (hE : GlRel E) : GlRel (EX E) := by
  intro a b c d
  have key : ∀ x y s t : A[X], (∀ p, s * p = p * s) → (∀ p, t * p = p * t) →
      (x + s) * (y + t) - (y + t) * (x + s) = x * y - y * x := by
    intro x y s t hs ht
    rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, hs y, hs t, ht x]
    abel
  have hs : ∀ (P : Prop) [Decidable P] (p : A[X]), (if P then X else 0) * p = p * (if P then X else 0) := by
    intro P _ p
    split_ifs
    · exact X_mul
    · simp
  unfold EX
  rw [key _ _ _ _ (hs _) (hs _), ← C_mul, ← C_mul, ← C_sub, hE a b c d]
  by_cases h1 : b = c <;> by_cases h2 : d = a
  · subst h1; subst h2; simp
  · simp [h1, h2, Ne.symm h2]
  · simp [h1, h2, Ne.symm h1]
  · simp [h1, h2]
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
