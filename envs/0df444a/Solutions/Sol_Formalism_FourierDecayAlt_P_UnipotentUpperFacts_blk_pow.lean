-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentUpperFacts.blk_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:45:46.813877+00:00
-- url     : https://prove2.me/submissions/fb489443-5265-4b80-9245-6f2b83c3f92d

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
theorem _root_.solution {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) (m : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ m = Matrix.fromBlocks (A ^ m) 0 0 (D ^ m) := by
  induction m with
  | zero => simp [Matrix.fromBlocks_one]
  | succ m ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]; simp
end Formalism.FourierDecayAlt.P.UnipotentUpperFacts
