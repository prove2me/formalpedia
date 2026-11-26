-- Prove2me | solution 1 for FourierJacobi.Valuations.central_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:49:55.248686+00:00
-- url     : https://prove2.me/submissions/01e29619-e241-4c44-b864-ea857a24b275

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
namespace FourierJacobi.Valuations
theorem _root_.solution (u v : ℤ) :
    2 * (u + v - max u v - max u (2 * v)) ≤ -max u v := by
  omega
end FourierJacobi.Valuations
