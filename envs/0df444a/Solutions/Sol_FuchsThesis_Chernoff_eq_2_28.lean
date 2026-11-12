-- Prove2me | solution 1 for FuchsThesis.Chernoff.eq_2_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:00:17.939196+00:00
-- url     : https://prove2.me/submissions/33f5f045-e61e-4108-825c-3d6b44271054

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_productDist
import Definitions.Def_FuchsThesis_Chernoff_errorProbN
import Definitions.Def_FuchsThesis_Chernoff_renyiOverlap

open CalibratedCE.Forecast

open FuchsThesis.Chernoff in
theorem solution {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (N : ℕ) :
    errorProbN π0 π1 p0 p1 N ≤
        π0 ^ α * π1 ^ (1 - α) *
          ∑ s : Fin N → B, productDist p0 N s ^ α * productDist p1 N s ^ (1 - α) ∧
      ∑ s : Fin N → B, productDist p0 N s ^ α * productDist p1 N s ^ (1 - α) =
        ∑ s : Fin N → B, ∏ k, p0 (s k) ^ α * p1 (s k) ^ (1 - α) ∧
      ∑ s : Fin N → B, ∏ k, p0 (s k) ^ α * p1 (s k) ^ (1 - α) =
        ∏ _k : Fin N, ∑ b, p0 b ^ α * p1 b ^ (1 - α) ∧
      ∏ _k : Fin N, ∑ b, p0 b ^ α * p1 b ^ (1 - α) = renyiOverlap p0 p1 α ^ N ∧
      π0 ^ α * π1 ^ (1 - α) * renyiOverlap p0 p1 α ^ N ≤ renyiOverlap p0 p1 α ^ N := by
  have hP0 : ∀ s, 0 ≤ productDist p0 N s := fun s => Finset.prod_nonneg (fun k _ => hp0.1 _)
  have hP1 : ∀ s, 0 ≤ productDist p1 N s := fun s => Finset.prod_nonneg (fun k _ => hp1.1 _)
  have hmin : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → min a b ≤ a ^ α * b ^ (1 - α) := by
    intro a b ha hb
    have hm0 : 0 ≤ min a b := le_min ha hb
    calc min a b = (min a b) ^ α * (min a b) ^ (1 - α) := by
          rw [← Real.rpow_add' hm0 (show α + (1 - α) ≠ 0 by norm_num), add_sub_cancel,
            Real.rpow_one]
      _ ≤ a ^ α * b ^ (1 - α) :=
          mul_le_mul (Real.rpow_le_rpow hm0 (min_le_left _ _) hα0)
            (Real.rpow_le_rpow hm0 (min_le_right _ _) (by linarith))
            (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg ha _)
  have hR : 0 ≤ renyiOverlap p0 p1 α :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (Real.rpow_nonneg (hp0.1 b) _)
      (Real.rpow_nonneg (hp1.1 b) _))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold errorProbN bayesError
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    calc min (π0 * productDist p0 N s) (π1 * productDist p1 N s)
        ≤ (π0 * productDist p0 N s) ^ α * (π1 * productDist p1 N s) ^ (1 - α) :=
          hmin _ _ (mul_nonneg hπ0 (hP0 s)) (mul_nonneg hπ1 (hP1 s))
      _ = π0 ^ α * π1 ^ (1 - α) * (productDist p0 N s ^ α * productDist p1 N s ^ (1 - α)) := by
          rw [Real.mul_rpow hπ0 (hP0 s), Real.mul_rpow hπ1 (hP1 s)]
          ring
  · apply Finset.sum_congr rfl
    intro s _
    simp only [productDist]
    rw [← Real.finsetProd_rpow _ _ (fun k _ => hp0.1 _),
      ← Real.finsetProd_rpow _ _ (fun k _ => hp1.1 _), ← Finset.prod_mul_distrib]
  · rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.sum_pow]
  · unfold renyiOverlap
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · have hc : π0 ^ α * π1 ^ (1 - α) ≤ 1 :=
      mul_le_one₀ (Real.rpow_le_one hπ0 (by linarith) hα0) (Real.rpow_nonneg hπ1 _)
        (Real.rpow_le_one hπ1 (by linarith) (by linarith))
    exact mul_le_of_le_one_left (pow_nonneg hR _) hc
