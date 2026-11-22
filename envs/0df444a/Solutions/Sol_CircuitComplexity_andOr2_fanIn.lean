-- Prove2me | solution 1 for CircuitComplexity.andOr2_fanIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:07.062958+00:00
-- url     : https://prove2.me/submissions/ba737d60-5fef-45b1-abd3-0e3f9669dd7a

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {W : Nat} (g : Gate Basis.andOr2 W) : g.fanIn = 2 := g.arityOk
end CircuitComplexity
