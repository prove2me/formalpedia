-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.type_sign_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:46.84881+00:00
-- url     : https://prove2.me/submissions/dad4edcf-d8bf-438a-96d0-0a2085f689ac

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
theorem _root_.solution : TypeSign := by
  intro q₁ d _ _ h1 h2 hdvd
  have o1 : Odd q₁ := Nat.odd_iff.2 (by omega)
  have o2 : Odd d := Nat.odd_iff.2 (by omega)
  have h : jacobiSym (-(d : ℤ)) q₁ = 1 := by
    have : (-(d : ℤ)) % (q₁ : ℤ) = 1 % (q₁ : ℤ) := by
      apply Int.modEq_iff_dvd.2
      have : ((q₁ : ℕ) : ℤ) ∣ ((d + 1 : ℕ) : ℤ) := by exact_mod_cast hdvd
      convert this using 1
      push_cast; ring
    rw [jacobiSym.mod_left' this, jacobiSym.one_left]
  refine ⟨h, ?_⟩
  rw [jacobiSym.neg _ o1, ZMod.χ₄_nat_three_mod_four (by omega)] at h
  rw [jacobiSym.neg _ o2, ZMod.χ₄_nat_three_mod_four (by omega),
    jacobiSym.quadratic_reciprocity_three_mod_four (by omega) (by omega)]
  linarith
end Formalism.HermitianLattices.ZeroFreeRegionGL2
