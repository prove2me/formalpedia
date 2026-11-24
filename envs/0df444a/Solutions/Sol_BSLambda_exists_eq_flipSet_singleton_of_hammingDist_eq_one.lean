-- Prove2me | solution 1 for BSLambda.exists_eq_flipSet_singleton_of_hammingDist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:49:30.016664+00:00
-- url     : https://prove2.me/submissions/2e21c343-7acf-4687-acf4-31b1ff208838

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]


theorem solution {x y : Input V}
    (h : hammingDist x y = 1) : ∃ v, y = flipSet x {v} := by
  classical
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h
  refine ⟨v,?_⟩; funext j
  have e : x j ≠ y j ↔ j = v := by
    have := Finset.ext_iff.mp hv j
    simpa using this
  by_cases h : j = v <;> cases hx : x j <;> cases hy : y j <;> simp_all [flipSet]
