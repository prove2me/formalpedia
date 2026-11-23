-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2a2.kronecker_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.640808+00:00
-- url     : https://prove2.me/submissions/2bee9315-db4c-462e-9f60-7122bf14c639

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ShortIntervalImpliesProgressionsStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2a2
open Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2a2
theorem _root_.solution : KronTwo := by
  intro q hq
  have hqo : Odd q := by rw [Nat.odd_iff]; omega
  rw [jacobiSym.at_two hqo]
  have h8 : q % 8 = 3 ∨ q % 8 = 7 := by omega
  have : ((q : ℕ) : ZMod 8) = ((q % 8 : ℕ) : ZMod 8) := by simp
  push_cast
  rw [this]
  rcases h8 with h | h <;> rw [h] <;> decide
end Formalism.HermitianLattices.GL2a2
