-- Prove2me | solution 1 for AvramDividend.Classical.positive_measure_ac_of_weighted_ac_and_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:44:51.855788+00:00
-- url     : https://prove2.me/submissions/f308ad26-1966-47c4-a763-9ed81586a255

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (U : Measure ℝ)
    (hSupport : U (Iio (0 : ℝ)) = 0)
    (hZero : U {(0 : ℝ)} = 0)
    (hWeighted : (U.withDensity (fun x : ℝ => ENNReal.ofReal x)) ≪
      (volume : Measure ℝ)) :
    U ≪ (volume : Measure ℝ) := by
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal x
  have hSet : Iic (0 : ℝ) = Iio 0 ∪ {(0 : ℝ)} := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · intro hx
      rcases hx with hlt | heq
      · exact le_of_lt hlt
      · exact heq ▸ le_rfl
  have hIic : U (Iic (0 : ℝ)) = 0 := by
    rw [hSet]
    exact measure_union_null hSupport hZero
  have hfMeas : Measurable f := by
    fun_prop
  have hfPos : ∀ᵐ x ∂U, f x ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hIic] with x hx
    have hxpos : 0 < x := lt_of_not_ge (by simpa only [mem_Iic] using hx)
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hxpos)
  have hfFin : ∀ᵐ x ∂U, f x ≠ ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_ne_top)
  have hRecover :
      ((U.withDensity f).withDensity (fun x => (f x)⁻¹)) = U :=
    withDensity_inv_same hfMeas hfPos hfFin
  have hBack :
      ((U.withDensity f).withDensity (fun x => (f x)⁻¹)) ≪
        (volume : Measure ℝ) :=
    (withDensity_absolutelyContinuous (U.withDensity f) _).trans
      (by simpa only [f] using hWeighted)
  exact hRecover ▸ hBack
