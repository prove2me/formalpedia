-- Prove2me | solution 1 for CircuitComplexity.CNF.size_toCircuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:13.859804+00:00
-- url     : https://prove2.me/submissions/aa7f4433-1a50-4cd6-a228-da5542cd8cfa

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
open CircuitComplexity.CNF
namespace CircuitComplexity.CNF
theorem _root_.solution [NeZero N] (φ : CNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl
end CircuitComplexity.CNF
