-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2a2.kronecker_odd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:34.495307+00:00
-- url     : https://prove2.me/submissions/7d431303-dbd1-4004-a73d-bd4a3cc81be1

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
theorem _root_.solution : KronOdd := by
  intro q n hq hn
  have hqo : Odd q := by rw [Nat.odd_iff]; omega
  rw [← neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hn]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h1 | h3
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hqo h1]
    rw [ZMod.χ₄_nat_one_mod_four h1, one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four hq h3]
    rw [ZMod.χ₄_nat_three_mod_four h3]; ring
end Formalism.HermitianLattices.GL2a2
