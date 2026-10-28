-- Prove2me | solution 1 for AvramDividend.Classical.finite_measure_cumulative_atom_integral_of_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:09:41.463568+00:00
-- url     : https://prove2.me/submissions/4dd220bf-69f1-4eca-8487-55b5824e583f

import Theorems.Thm_AvramDividend_Classical_nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped ENNReal

/-- A finite cumulative measure equals its nonpositive atom mass plus its density primitive. -/
theorem solution
    (β : Measure ℝ) (hβfin : β Set.univ ≠ ⊤)
    (f : ℝ → ℝ) (hfnn : ∀ y : ℝ, 0 ≤ f y)
    (hIoc : ∀ x : ℝ, 0 ≤ x →
      β (Ioc (0 : ℝ) x) =
        (volume.withDensity (fun y : ℝ => ENNReal.ofReal (f y)))
          (Ioc (0 : ℝ) x))
    (hfi : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x) :
    ∀ x : ℝ, 0 < x →
      (β (Iic x)).toReal =
        (β (Iic (0 : ℝ))).toReal + ∫ y in (0 : ℝ)..x, f y := by
  intro x hx
  have hunion : Iic (0 : ℝ) ∪ Ioc (0 : ℝ) x = Iic x := by
    ext y
    simp only [mem_union, mem_Iic, mem_Ioc]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact le_trans h (le_of_lt hx)
      · exact h
    · intro hy
      by_cases h0 : y ≤ 0
      · exact Or.inl h0
      · exact Or.inr ⟨lt_of_not_ge h0, hy⟩
  have hdisj : Disjoint (Iic (0 : ℝ)) (Ioc (0 : ℝ) x) := by
    apply Set.disjoint_left.mpr
    intro y hy0 hypos
    exact (not_lt_of_ge hy0) hypos.1
  have hfinSet (s : Set ℝ) : β s ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ s))
      (lt_top_iff_ne_top.mpr hβfin)
  have hadd :
      β (Iic x) = β (Iic (0 : ℝ)) + β (Ioc (0 : ℝ) x) := by
    rw [← hunion]
    exact measure_union hdisj measurableSet_Ioc
  rw [hadd, ENNReal.toReal_add (hfinSet _) (hfinSet _),
      hIoc x (le_of_lt hx)]
  rw [nonnegative_real_density_Ioc_toReal_eq_intervalIntegral
    f hfnn x (le_of_lt hx) (hfi x hx)]