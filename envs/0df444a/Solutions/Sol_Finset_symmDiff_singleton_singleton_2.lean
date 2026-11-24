-- Prove2me | solution 2 for Finset.symmDiff_singleton_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:54:47.879627+00:00
-- url     : https://prove2.me/submissions/fa12476b-5cca-4d7e-a50f-82651e9a52ae

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube

set_option autoImplicit true
@[expose] public section
public section
namespace Finset
theorem _root_.solution {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by
  ext v
  by_cases h1 : v = p <;> by_cases h2 : v = q <;> simp_all [Finset.mem_symmDiff]
end Finset
