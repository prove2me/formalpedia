-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.lemma2a_normal_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:35:28.784817+00:00
-- url     : https://prove2.me/submissions/4691ad73-1014-4714-802e-248b030ef114

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace P4cb19dd8

lemma tail_eq (z : ℝ) :
    1 - cdf (gaussianReal 0 1) z = (gaussianReal 0 1).real (Ioi z) := by
  rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

lemma half_eq : (gaussianReal 0 1).real (Ioi (0:ℝ)) = 1 / 2 := by
  set ν := gaussianReal (0:ℝ) 1 with hν
  have hsymm : ν.real (Ioi 0) = ν.real (Iio 0) := by
    have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
    rw [neg_zero] at h
    have : ν.real (Ioi 0) = (ν.map (fun x : ℝ ↦ -x)).real (Ioi 0) := by rw [hν, h]
    rw [this, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext x; simp
  have hzero : ν.real {0} = 0 := by
    have hac := gaussianReal_absolutelyContinuous (0:ℝ) (v := 1) one_ne_zero
    have h0 : ν {0} = 0 := hac (Real.volume_singleton)
    simp [Measure.real, h0]
  have hunion : ν.real (Iio 0) + ν.real {0} + ν.real (Ioi 0) = 1 := by
    have h1 : Iio (0:ℝ) ∪ {0} ∪ Ioi 0 = univ := by
      ext x; simp only [mem_union, mem_Iio, mem_singleton_iff, mem_Ioi, mem_univ, iff_true]
      rcases lt_trichotomy x 0 with h | h | h <;> simp [h]
    rw [← measureReal_union, ← measureReal_union, h1, probReal_univ]
    · rw [disjoint_union_left]; constructor
      · exact Iio_disjoint_Ioi_of_le le_rfl
      · simp
    · exact measurableSet_Ioi
    · simp
    · exact measurableSet_singleton 0
  linarith

lemma exp_half_gt : (1:ℝ) / 2 < Real.exp (-(1/2)) := by
  have h1 : Real.exp (1/2) * Real.exp (1/2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h2 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; linarith
  have h3 : Real.exp (1/2) < 2 := by
    nlinarith [Real.exp_pos (1/2)]
  rw [Real.exp_neg]
  rw [lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
  linarith

lemma chernoff (z : ℝ) (hz : 0 ≤ z) :
    (gaussianReal 0 1).real (Ioi z) ≤ Real.exp (-(z ^ 2 / 2)) := by
  have hc := measure_ge_le_exp_mul_mgf (μ := gaussianReal (0:ℝ) 1) (X := id) z hz
    (integrable_exp_mul_gaussianReal z)
  rw [mgf_id_gaussianReal] at hc
  have hsub : Ioi z ⊆ {ω : ℝ | z ≤ id ω} := fun x hx => show z ≤ x from le_of_lt hx
  calc (gaussianReal 0 1).real (Ioi z) ≤ (gaussianReal 0 1).real {ω : ℝ | z ≤ id ω} :=
        measureReal_mono hsub
    _ ≤ _ := hc
    _ = Real.exp (-(z ^ 2 / 2)) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring

end P4cb19dd8

theorem solution (z : ℝ) (hz : 0 ≤ z) :
    1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) z < Real.exp (-(1 / 2) * z) := by
  rw [P4cb19dd8.tail_eq]
  rcases le_or_gt z 1 with h1 | h1
  · calc (ProbabilityTheory.gaussianReal 0 1).real (Ioi z)
          ≤ (ProbabilityTheory.gaussianReal 0 1).real (Ioi 0) := measureReal_mono (Ioi_subset_Ioi hz)
      _ = 1 / 2 := P4cb19dd8.half_eq
      _ < Real.exp (-(1/2)) := P4cb19dd8.exp_half_gt
      _ ≤ Real.exp (-(1 / 2) * z) := by
          apply Real.exp_le_exp.mpr; nlinarith
  · calc (ProbabilityTheory.gaussianReal 0 1).real (Ioi z) ≤ Real.exp (-(z ^ 2 / 2)) := P4cb19dd8.chernoff z hz
      _ < Real.exp (-(1 / 2) * z) := by
          apply Real.exp_lt_exp.mpr; nlinarith
