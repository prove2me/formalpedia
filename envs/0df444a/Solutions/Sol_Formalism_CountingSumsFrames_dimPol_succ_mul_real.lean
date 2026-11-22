-- Prove2me | solution 1 for Formalism.CountingSumsFrames.dimPol_succ_mul_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:48.518986+00:00
-- url     : https://prove2.me/submissions/5e7dc70e-53f3-4fc6-af04-fc029e52e473

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' A : ℕ) :
    (dimPol k' (A + 1) : ℝ) * ((A : ℝ) + 1) = dimPol k' A * ((A : ℝ) + 1 + k') := by
  have h := Nat.choose_mul_succ_eq (A + k') k'
  rw [show A + k' + 1 - k' = A + 1 by omega] at h
  have h3 : dimPol k' (A + 1) * (A + 1) = dimPol k' A * (A + 1 + k') := by
    unfold dimPol
    rw [show A + 1 + k' = A + k' + 1 by omega]
    exact h.symm
  exact_mod_cast h3
end Formalism.CountingSumsFrames
