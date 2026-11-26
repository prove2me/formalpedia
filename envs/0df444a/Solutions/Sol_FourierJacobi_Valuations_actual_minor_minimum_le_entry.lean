-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_minor_minimum_le_entry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:05.876081+00:00
-- url     : https://prove2.me/submissions/dc6dcce3-f16c-4441-868f-c00e631b6603

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Theorems.Thm_FourierJacobi_Valuations_actual_entry_minimum
import Theorems.Thm_FourierJacobi_Valuations_actual_minor_minimum
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (a x y z : K) (ha : a ≠ 0) :
    matrixMinimum v (secondCompound (g a x y z)) ≤ matrixMinimum v (g a x y z) := by
  rw [actual_minor_minimum v a x y z ha, actual_entry_minimum]
  have hz : minorListMinimum v a x y z ≤ v z := by
    obtain ⟨k,hk⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr ha)
    have hva : v a = (k : WithTop ℤ) := hk.symm
    have hvi : v a⁻¹ = ((-k : ℤ) : WithTop ℤ) := by simp [hva]
    rcases le_total k 0 with h | h
    · have hka : v a ≤ 0 := by rw [hva]; exact_mod_cast h
      have he : v (a*z) ≤ v z := by
        rw [v.map_mul]
        simpa [add_comm] using add_le_add_right hka (v z)
      exact le_trans (by simp [minorListMinimum]) he
    · have hka : v a⁻¹ ≤ 0 := by
        rw [hvi]
        exact_mod_cast neg_nonpos.mpr h
      have he : v (z/a) ≤ v z := by
        rw [div_eq_mul_inv, v.map_mul]
        simpa [add_comm] using add_le_add_left hka (v z)
      exact le_trans (by simp [minorListMinimum]) he
  simp only [entryListMinimum, le_min_iff]
  exact ⟨⟨⟨⟨⟨⟨by simp [minorListMinimum], by simp [minorListMinimum]⟩,
    by simp [minorListMinimum]⟩, by simp [minorListMinimum]⟩,
    by simp [minorListMinimum]⟩, by simp [minorListMinimum]⟩, hz⟩
end FourierJacobi.Valuations
