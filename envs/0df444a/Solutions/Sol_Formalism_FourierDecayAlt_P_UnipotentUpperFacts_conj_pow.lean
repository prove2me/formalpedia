-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentUpperFacts.conj_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:39:10.077103+00:00
-- url     : https://prove2.me/submissions/663d7476-cb51-45dd-bab9-129651d586d5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.UnipotentUpperFacts
theorem _root_.solution (γ X : Matrix n n ℂ) (hγ : IsUnit γ.det) (p : ℕ) : (γ⁻¹ * X * γ) ^ p = γ⁻¹ * X ^ p * γ := by
  induction p with
  | zero => simp [Matrix.nonsing_inv_mul _ hγ]
  | succ p ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
end Formalism.FourierDecayAlt.P.UnipotentUpperFacts
