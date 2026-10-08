-- Prove2me | solution 1 for BBBV.RandomPermutation.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:02:50.979933+00:00
-- url     : https://prove2.me/submissions/57428cf1-12ff-4208-9fa2-e6e35a3c2a0c

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_QueryModel

theorem solution {ι : Type} [Fintype ι] (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ε : ℝ) (h : ‖u - v‖ ≤ ε) :
    (∑ c : ι, |‖u c‖ ^ 2 - ‖v c‖ ^ 2|) ≤ 4 * ε := by
  classical
  let U : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖u i‖)
  let V : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖v i‖)
  let D : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ‖(u - v) i‖)
  have hU : ‖U‖ = 1 := by
    have hs : ‖U‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg U]
  have hV : ‖V‖ = 1 := by
    have hs : ‖V‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg V]
  have hD : ‖D‖ = ‖u - v‖ := by
    have hs : ‖D‖ ^ 2 = ‖u - v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    nlinarith [norm_nonneg D, norm_nonneg (u - v)]
  have hb : (∑ c, |‖u c‖ ^ 2 - ‖v c‖ ^ 2|) ≤ inner ℝ D (U + V) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_le_sum
    intro c hc
    simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
      WithLp.ofLp_add, Pi.add_apply]
    rw [mul_comm]
    change |‖u c‖ ^ 2 - ‖v c‖ ^ 2| ≤ ‖u c - v c‖ * (‖u c‖ + ‖v c‖)
    calc
      _ = |‖u c‖ - ‖v c‖| * (‖u c‖ + ‖v c‖) := by
        rw [← abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), ← abs_mul]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  have hn : ‖U + V‖ ≤ 2 := by
    have hh := norm_add_le U V
    rw [hU, hV] at hh
    norm_num at hh ⊢
    exact hh
  have he : 0 ≤ ε := (norm_nonneg _).trans h
  calc
    _ ≤ inner ℝ D (U + V) := hb
    _ ≤ ‖D‖ * ‖U + V‖ := real_inner_le_norm _ _
    _ ≤ ‖u - v‖ * 2 := by rw [hD]; gcongr
    _ ≤ 4 * ε := by nlinarith

#print axioms solution
