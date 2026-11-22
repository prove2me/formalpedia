-- Prove2me | solution 1 for CircuitComplexity.DNF.size_toCircuit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:22.073125+00:00
-- url     : https://prove2.me/submissions/4a316370-951b-4ffd-bca3-eb80024f9cbe

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
open CircuitComplexity.DNF
namespace CircuitComplexity.DNF
theorem _root_.solution [NeZero N] (φ : DNF N) :
    φ.toCircuit.size = φ.complexity + 1 := rfl
end CircuitComplexity.DNF
