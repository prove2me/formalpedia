-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.bad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:41.722796+00:00
-- url     : https://prove2.me/submissions/b6052faf-8cb0-4947-ab2f-fb81e4ce42c9

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (X : ℕ) (hX : 1 ≤ X) :
    (badCount S X : ℝ) ≤ C * (X : ℝ) ^ (1 - D) :=
  h.2.2.2 X hX
end PowerDense
end FirstPassageLinearTransport
