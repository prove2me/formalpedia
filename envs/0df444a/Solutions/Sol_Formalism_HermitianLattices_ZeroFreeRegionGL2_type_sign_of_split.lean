-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.type_sign_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:07.632055+00:00
-- url     : https://prove2.me/submissions/a92ccc6a-4ef8-471c-a307-5820fed30133

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : TypeSignOfSplit := by
  intro q₁ d h1 h2 h
  have o1 : Odd q₁ := Nat.odd_iff.2 (by omega)
  have o2 : Odd d := Nat.odd_iff.2 (by omega)
  rw [jacobiSym.neg _ o1, ZMod.χ₄_nat_three_mod_four h1] at h
  rw [jacobiSym.neg _ o2, ZMod.χ₄_nat_three_mod_four h2, jacobiSym.quadratic_reciprocity_three_mod_four h1 h2]
  linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
