-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.flipTwoThree.hook_den_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:57.164619+00:00
-- url     : https://prove2.me/submissions/c698b4e6-64fe-423a-a8b7-fce8bde91f13

import Definitions.Def_Formalism_LogVandermondeBounds_MultinomialPowerBound
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.flipTwoThree
open Finset MeasureTheory
namespace Formalism.LogVandermondeBounds.flipTwoThree
theorem _root_.solution (N : ℕ) (nu : Fin (N+1) → ℕ) (hnu : Antitone nu) (i j : Fin (N+1))
    (hij : i < j) :
    (1:ℝ) ≤ (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ∧
      (((nu i : ℤ) - nu j + j - i : ℤ) : ℝ) ≤ (nu 0 : ℝ) + N + 1 := by
  have h1 : nu j ≤ nu i := hnu hij.le
  have h2 : nu i ≤ nu 0 := hnu (Fin.zero_le i)
  have h3 : (i:ℕ) < j := hij
  have h4 : (j:ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
  constructor
  · have : (1:ℤ) ≤ (nu i : ℤ) - nu j + j - i := by omega
    exact_mod_cast this
  · have : ((nu i : ℤ) - nu j + j - i) ≤ (nu 0 : ℤ) + N + 1 := by omega
    exact_mod_cast this
end Formalism.LogVandermondeBounds.flipTwoThree
