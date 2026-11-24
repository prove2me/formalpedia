-- Prove2me | solution 1 for CyclotomicIntegers.powerBasis_dim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:54.871168+00:00
-- url     : https://prove2.me/submissions/85b51bf9-3202-49b7-8df5-beca3d26b72d

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
theorem _root_.solution : (powerBasis p).dim = p - 1 := by
  simp [powerBasis, Nat.totient_prime hpri.out, natDegree_cyclotomic]
end CyclotomicIntegers
