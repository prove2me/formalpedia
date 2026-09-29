-- Prove2me | solution 1 for ChatterjeeSamuelson.LinkedODE.offer_cdf_eq_value_cdf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:48:04.510037+00:00
-- url     : https://prove2.me/submissions/f7ccbf71-097f-45fd-bcde-be18ec83aa62

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- Under a regular belief, almost every value lies in `[lo, hi]`. -/
theorem aux_ocdf_ae_mem (μb : Measure ℝ) (loS hiS : ℝ) (fb : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) : ∀ᵐ x ∂μb, x ∈ Icc loS hiS := by
  obtain ⟨hP, -, hlo, hhi, -, -⟩ := hμb
  have := hP
  have h1 : μb (Iic loS) = 0 := by
    rw [← ofReal_cdf, hlo, ENNReal.ofReal_zero]
  have h2 : μb (Iic hiS) = 1 := by
    rw [← ofReal_cdf, hhi, ENNReal.ofReal_one]
  have h3 : μb (Ioi hiS) = 0 := by
    rw [← compl_Iic, prob_compl_eq_zero_iff measurableSet_Iic]
    exact h2
  have hIio : μb (Iio loS) = 0 := measure_mono_null Iio_subset_Iic_self h1
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null hIio h3)
  intro x hx
  simp only [mem_ofPred_eq, mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact Or.inl hx
  · exact Or.inr hx

end ChatterjeeSamuelson.LinkedODE

open ChatterjeeSamuelson.LinkedODE

theorem solution (μb : Measure ℝ) (loS hiS : ℝ) (fb S : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hS : ClassA S loS hiS)
    (a c y : ℝ) (ha : loS ≤ a) (hc : c ≤ hiS) (hy : y ∈ Ioo a c)
    (hmono : StrictMonoOn S (Ioo a c)) :
    (μb {vs | S vs ≤ S y}).toReal = cdf μb y := by
  have hP : IsProbabilityMeasure μb := hμb.1
  obtain ⟨hbddA, hbddB, hmon, hflat, -⟩ := hS
  have hyI : y ∈ Icc loS hiS := ⟨ha.trans hy.1.le, hy.2.le.trans hc⟩
  -- points of `(a, c)` on both sides of `y`
  obtain ⟨y1, hy1a, hy1y⟩ := exists_between hy.1
  obtain ⟨y2, hy2y, hy2c⟩ := exists_between hy.2
  have hy1 : y1 ∈ Ioo a c := ⟨hy1a, hy1y.trans hy.2⟩
  have hy2 : y2 ∈ Ioo a c := ⟨hy.1.trans hy2y, hy2c⟩
  have hy1I : y1 ∈ Icc loS hiS := ⟨ha.trans hy1a.le, (hy1.2.le).trans hc⟩
  have hy2I : y2 ∈ Icc loS hiS := ⟨ha.trans hy2.1.le, hy2c.le.trans hc⟩
  have hS1 : S y1 < S y := hmono hy1 hy hy1y
  have hS2 : S y < S y2 := hmono hy hy2 hy2y
  have hinf : sInf (S '' Icc loS hiS) < S y :=
    lt_of_le_of_lt (csInf_le hbddB (mem_image_of_mem S hy1I)) hS1
  have hsup : S y < sSup (S '' Icc loS hiS) :=
    lt_of_lt_of_le hS2 (le_csSup hbddA (mem_image_of_mem S hy2I))
  -- the two sets agree on `[loS, hiS]`
  have key : ∀ x ∈ Icc loS hiS, (S x ≤ S y ↔ x ≤ y) := by
    intro x hx
    constructor
    · intro h
      by_contra hxy
      rw [not_le] at hxy
      have hge : S y ≤ S x := hmon hyI hx hxy.le
      have heq : S y = S x := le_antisymm hge h
      rcases hflat y hyI x hx (ne_of_lt hxy) heq with h' | h'
      · exact absurd h' (ne_of_gt hinf)
      · exact absurd h' (ne_of_lt hsup)
    · intro h
      exact hmon hx hyI h
  have hae : {vs | S vs ≤ S y} =ᵐ[μb] Iic y := by
    filter_upwards [aux_ocdf_ae_mem μb loS hiS fb hμb] with x hx
    change (S x ≤ S y) = (x ≤ y)
    exact propext (key x hx)
  rw [measure_congr hae, cdf_eq_real, measureReal_def]
