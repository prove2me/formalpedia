-- Prove2me | solution 1 for CircuitComplexity.full_term_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:43.772653+00:00
-- url     : https://prove2.me/submissions/66715638-7924-4a4b-a2eb-3a373b75e3d7

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity
namespace CircuitComplexity
theorem _root_.solution {term : List (Literal N)}
    (hfull : ∀ i : Fin N, ∃ l ∈ term, l.var = i)
    {x y : BitString N}
    (hx : term.all (fun l => l.eval x) = true)
    (hy : term.all (fun l => l.eval y) = true) :
    x = y := by
  funext i
  obtain ⟨l, hl_mem, hl_var⟩ := hfull i
  rw [List.all_eq_true] at hx hy
  have hx_l := hx l hl_mem
  have hy_l := hy l hl_mem
  simp only [Literal.eval, hl_var] at hx_l hy_l
  split at hx_l <;> split at hy_l <;> simp_all
end CircuitComplexity
