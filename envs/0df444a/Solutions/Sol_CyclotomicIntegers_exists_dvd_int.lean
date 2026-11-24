-- Prove2me | solution 1 for CyclotomicIntegers.exists_dvd_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:54.287786+00:00
-- url     : https://prove2.me/submissions/7cac2c73-cc16-4f39-b8c5-648b07326f4b

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
theorem _root_.solution (n : CyclotomicIntegers p) (hn : n ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ n ∣ m := by
  refine ⟨Algebra.norm ℤ ((equiv p) n), by simpa, ?_⟩
  rw [← map_dvd_iff (equiv p), map_intCast]
  have : IsGalois ℚ (CyclotomicField p ℚ) := IsCyclotomicExtension.isGalois {p} _ _
  convert RingOfIntegers.dvd_norm ℚ (equiv p n) using 1
  ext1
  exact DFunLike.congr_arg (algebraMap ℚ _) (Algebra.coe_norm_int (equiv p n))
end CyclotomicIntegers
