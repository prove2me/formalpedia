-- Prove2me | solution 1 for Erdos679.primeProduct_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:47.821859+00:00
-- url     : https://prove2.me/submissions/22be172d-5d4d-44a0-8f34-5cea202c8dd7

module
public import Definitions.Def_Erdos679_StirlingBound
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_Analytic
public import Theorems.Thm_Erdos679_primeProduct_strictMono

set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679
namespace Erdos679
theorem _root_.solution : Tendsto primeProduct atTop atTop :=
  primeProduct_strictMono.tendsto_atTop
end Erdos679
