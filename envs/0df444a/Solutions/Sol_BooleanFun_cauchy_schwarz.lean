-- Prove2me | solution 1 for BooleanFun.cauchy_schwarz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:56.465743+00:00
-- url     : https://prove2.me/submissions/1515e2e5-440f-412f-a62b-bcac02554299

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution : |⟪f, g⟫| ≤ ‖f‖ * ‖g‖ :=
  norm_inner_le_norm (𝕜 := ℝ) f g
end BooleanFun
