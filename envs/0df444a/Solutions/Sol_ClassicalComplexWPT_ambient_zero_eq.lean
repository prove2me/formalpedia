-- Prove2me | solution 1 for ClassicalComplexWPT.ambient_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:10.912818+00:00
-- url     : https://prove2.me/submissions/7065a41c-0fc7-4852-80a7-4307db5dfe00

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_ClassicalComplexWPT_Basic

set_option autoImplicit true
open scoped BigOperators Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution (n : ℕ) : (0 : Ambient n) = ((0 : Base n), 0) := by
  ext <;> simp
end ClassicalComplexWPT
