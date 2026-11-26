-- Prove2me | solution 1 for FirstPassageLinearTransport.cosh_int_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:43.301582+00:00
-- url     : https://prove2.me/submissions/4a005432-6261-4dfd-a6d1-26fde3211d7a

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution (θ : ℝ) (y : ℤ) :
    Real.cosh (θ * ((y - 1 : ℤ) : ℝ)) +
        Real.cosh (θ * ((y + 1 : ℤ) : ℝ)) =
      2 * Real.cosh (θ * (y : ℝ)) * Real.cosh θ := by
  rw [show θ * ((y - 1 : ℤ) : ℝ) = θ * (y : ℝ) - θ by push_cast; ring]
  rw [show θ * ((y + 1 : ℤ) : ℝ) = θ * (y : ℝ) + θ by push_cast; ring]
  rw [Real.cosh_sub, Real.cosh_add]
  ring
end FirstPassageLinearTransport
