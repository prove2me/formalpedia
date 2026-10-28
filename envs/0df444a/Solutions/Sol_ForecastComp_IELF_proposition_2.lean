-- Prove2me | solution 1 for ForecastComp.IELF.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:02:21.46703+00:00
-- url     : https://prove2.me/submissions/333b51e8-7311-431d-99d6-ff061e62883e

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

open MeasureTheory

open ForecastComp.IELF in
theorem solution {m n : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (R : ℝ → Bool → ℝ)
    (θ : Measure (Fin m → Bool)) [IsProbabilityMeasure θ]
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k, y j k ∈ Set.Icc (0:ℝ) 1) (i : Fin n) :
    ∫ x, elfMultiProb R y x i ∂θ =
      1 / (n:ℝ) + 1 / (n:ℝ) * (avgScoreJoint R θ (y i) -
        1 / ((n:ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, avgScoreJoint R θ (y j)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpt : ∀ x : Fin m → Bool, elfMultiProb R y x i =
      1 / (n:ℝ) + 1 / (n:ℝ) * (1 / (m:ℝ) * ∑ k, R (y i k) (x k))
        - 1 / (n:ℝ) * (1 / ((n:ℝ) - 1)) *
          ∑ j ∈ Finset.univ.erase i, (1 / (m:ℝ) * ∑ k, R (y j k) (x k)) := by
    intro x
    simp only [elfMultiProb, elfProb]
    have S1 : ∑ k : Fin m, (1 / (n:ℝ) + 1 / (n:ℝ) * (R (y i k) (x k) -
          1 / ((n:ℝ) - 1) * ∑ j ∈ Finset.univ.erase i, R (y j k) (x k))) =
        (m:ℝ) * (1 / (n:ℝ)) + 1 / (n:ℝ) * ∑ k, R (y i k) (x k) -
          1 / (n:ℝ) * (1 / ((n:ℝ) - 1)) * ∑ k : Fin m, ∑ j ∈ Finset.univ.erase i, R (y j k) (x k) := by
      simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [S1, Finset.sum_comm]
    have hC : ∑ j ∈ Finset.univ.erase i, (1 / (m:ℝ) * ∑ k, R (y j k) (x k)) =
        1 / (m:ℝ) * ∑ j ∈ Finset.univ.erase i, ∑ k, R (y j k) (x k) := (Finset.mul_sum _ _ _).symm
    rw [hC]
    field_simp
  rw [show (fun x => elfMultiProb R y x i) = _ from funext hpt]
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const, probReal_univ,
    smul_eq_mul, one_mul,
    integral_const_mul (1 / (n:ℝ)) (fun x : Fin m → Bool => 1 / (m:ℝ) * ∑ k, R (y i k) (x k)),
    integral_const_mul (1 / (n:ℝ) * (1 / ((n:ℝ) - 1)))
      (fun x : Fin m → Bool => ∑ j ∈ Finset.univ.erase i, (1 / (m:ℝ) * ∑ k, R (y j k) (x k))),
    integral_finsetSum (Finset.univ.erase i)
      (f := fun j (x : Fin m → Bool) => 1 / (m:ℝ) * ∑ k, R (y j k) (x k))
      (fun j _ => Integrable.of_finite)]
  unfold avgScoreJoint
  ring
