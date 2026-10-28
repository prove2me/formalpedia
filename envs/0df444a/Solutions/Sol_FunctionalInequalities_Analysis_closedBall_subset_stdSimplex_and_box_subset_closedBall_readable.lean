-- Prove2me | solution 1 for FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:09.858999+00:00
-- url     : https://prove2.me/submissions/ceb230a4-1812-426d-b5e1-194363bdb561

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization

noncomputable section
open Set Matrix
section LT11D3SimplexBall
open Set Metric
private lemma FunctionalInequalities.Analysis.sum_abs_sub_le_sqrt_mul_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, |x i| ≤ Real.sqrt n * ‖x‖ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => |x i|) (fun _ => (1 : ℝ))
  have hcs' : (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := by
    simpa only [mul_one, one_pow, sq_abs, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul] using hcs
  have hnorm : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
    calc
      ‖x‖ ^ 2 = (Real.sqrt (∑ i, ‖x i‖ ^ 2)) ^ 2 := by
        rw [EuclideanSpace.norm_eq]
      _ = ∑ i, ‖x i‖ ^ 2 := by
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖x i‖))
      _ = ∑ i, x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.norm_eq_abs, sq_abs]
  have hsq : (∑ i, |x i|) ^ 2 ≤ (Real.sqrt n * ‖x‖) ^ 2 := by
    calc
      (∑ i, |x i|) ^ 2 ≤ (∑ i, x i ^ 2) * (n : ℝ) := hcs'
      _ = ‖x‖ ^ 2 * (n : ℝ) := by rw [← hnorm]
      _ = (Real.sqrt n * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        ring
  exact
    (sq_le_sq₀
      (Finset.sum_nonneg (fun i _ => abs_nonneg (x i)))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp hsq
private lemma FunctionalInequalities.Analysis.barycentre_ofLp_apply {n : ℕ} (i : Fin n) :
    (((1 / ((n : ℝ) + 1)) • ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i)
      = 1 / ((n : ℝ) + 1) := by
  simp [Finset.sum_apply]
/-- **The standard simplex contains a ball around its barycentre, and the coordinate box lies in a
ball** (weak Letwin route, Caffarelli's argument). -/
theorem solution {n : ℕ} (hn : 0 < n) :
    closedBall ((1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ))
        (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) ⊆
      {y : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ 1} ∧
    {y : EuclideanSpace ℝ (Fin n) | (∀ i, |y i| ≤ 1) ∧ |1 - ∑ i, y i| ≤ 1} ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) := by
  constructor
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    constructor
    · intro i
      have hi :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            ‖y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        have hi' := PiLp.norm_apply_le
          (y - ((1 / ((n : ℝ) + 1)) •
            ∑ j, EuclideanSpace.single j (1 : ℝ))) i
        rw [Real.norm_eq_abs] at hi'
        have hcoord :
            (y - ((1 / ((n : ℝ) + 1)) •
              ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1) := by
          change y.ofLp i -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
              y.ofLp i - 1 / ((n : ℝ) + 1)
          rw [FunctionalInequalities.Analysis.barycentre_ofLp_apply]
        rw [hcoord] at hi'
        exact hi'
      have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
      have hdenpos : 0 < 2 * ((n : ℝ) + 1) := by
        positivity
      have hdenle :
          2 * ((n : ℝ) + 1) ≤
            2 * ((n : ℝ) + 1) * Real.sqrt n := by
        have hnonneg : 0 ≤ 2 * ((n : ℝ) + 1) := by
          positivity
        have hdiff : 0 ≤ Real.sqrt n - 1 := sub_nonneg.mpr hsqrt
        nlinarith [mul_nonneg hnonneg hdiff]
      have hρ :
          1 / (2 * ((n : ℝ) + 1) * Real.sqrt n) ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        one_div_le_one_div_of_le hdenpos hdenle
      have hiρ :
          |y i - 1 / ((n : ℝ) + 1)| ≤
            1 / (2 * ((n : ℝ) + 1)) :=
        le_trans (le_trans hi hy) hρ
      have hlow :
          1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) ≤ y i := by
        have h := (abs_le.mp hiρ).1
        linarith
      have hnonneg :
          0 ≤ 1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) := by
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have heq :
            1 / ((n : ℝ) + 1) - 1 / (2 * ((n : ℝ) + 1)) =
              1 / (2 * ((n : ℝ) + 1)) := by
          field_simp [ne_of_gt hn1]
          ring
        rw [heq]
        positivity
      exact le_trans hnonneg hlow
    · have hsumabs :
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| ≤
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, |y i - 1 / ((n : ℝ) + 1)| =
              ∑ i, |(y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i| := by
                apply Finset.sum_congr rfl
                intro i hi
                have hcoord :
                    (y - ((1 / ((n : ℝ) + 1)) •
                      ∑ j, EuclideanSpace.single j (1 : ℝ))).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1) := by
                  change y.ofLp i -
                      ((1 / ((n : ℝ) + 1)) •
                        ∑ j, EuclideanSpace.single j (1 : ℝ)).ofLp i =
                      y.ofLp i - 1 / ((n : ℝ) + 1)
                  rw [FunctionalInequalities.Analysis.barycentre_ofLp_apply]
                rw [hcoord]
          _ ≤ Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ :=
            FunctionalInequalities.Analysis.sum_abs_sub_le_sqrt_mul_norm _
      have hsum :
          ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
        calc
          ∑ i, y i ≤
              ∑ i, (1 / ((n : ℝ) + 1) +
                |y i - 1 / ((n : ℝ) + 1)|) := by
            apply Finset.sum_le_sum
            intro i hi
            linarith [le_abs_self (y i - 1 / ((n : ℝ) + 1))]
          _ = ∑ i, (1 / ((n : ℝ) + 1)) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_add_distrib]
          _ = n / ((n : ℝ) + 1) +
              ∑ i, |y i - 1 / ((n : ℝ) + 1)| := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            ring
          _ ≤ n / ((n : ℝ) + 1) +
              Real.sqrt n * ‖y -
                ((1 / ((n : ℝ) + 1)) •
                  ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := by
            simpa [add_comm] using
              add_le_add_left hsumabs (n / ((n : ℝ) + 1))
      calc
        ∑ i, y i ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n * ‖y -
              ((1 / ((n : ℝ) + 1)) •
                ∑ j, EuclideanSpace.single j (1 : ℝ))‖ := hsum
        _ ≤ n / ((n : ℝ) + 1) +
            Real.sqrt n *
              (1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)) := by
          gcongr
        _ = n / ((n : ℝ) + 1) +
            1 / (2 * ((n : ℝ) + 1)) := by
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
          have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
          field_simp [ne_of_gt hsqrtpos]
        _ ≤ 1 := by
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          field_simp [ne_of_gt hn1]
          nlinarith
  · intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero]
    have hsq : ‖y‖ ^ 2 ≤ (n : ℝ) := by
      calc
        ‖y‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
          rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
          exact Finset.sum_nonneg (fun i _ => sq_nonneg (‖y i‖))
        _ ≤ ∑ i, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Real.norm_eq_abs, sq_abs]
          exact (sq_le_one_iff_abs_le_one (y i)).mpr (hy.1 i)
        _ = (n : ℝ) := by
          simp
    have hnorm : 0 ≤ ‖y‖ := norm_nonneg _
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact (sq_le_sq₀ hnorm hsqrt).mp (by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      exact hsq)
