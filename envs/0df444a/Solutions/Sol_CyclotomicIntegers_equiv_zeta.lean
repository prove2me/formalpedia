-- Prove2me | solution 1 for CyclotomicIntegers.equiv_zeta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:22.671807+00:00
-- url     : https://prove2.me/submissions/b051fa22-0644-4c8e-8fb6-6cc72fc0cd85

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_CyclotomicRing

set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Polynomial NumberField
variable (p : ℕ) [hpri : Fact p.Prime]
open CyclotomicIntegers
namespace CyclotomicIntegers
theorem _root_.solution : equiv p (zeta p) = (IsCyclotomicExtension.zeta_spec
    p ℚ (CyclotomicField p ℚ)).toInteger := by
  simp [equiv_apply, zeta]
end CyclotomicIntegers
