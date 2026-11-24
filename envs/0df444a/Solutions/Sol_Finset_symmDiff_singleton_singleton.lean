-- Prove2me | solution 1 for Finset.symmDiff_singleton_singleton
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:52:19.792791+00:00
-- url     : https://prove2.me/submissions/2c1926af-7095-443d-a268-68165d110605

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section


theorem solution {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by
  ext j; by_cases h : j = p <;> by_cases e : j = q <;> simp_all [Finset.mem_symmDiff]
