-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.t_BoxSumLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:41.358829+00:00
-- url     : https://prove2.me/submissions/352a79e1-2cc5-4590-8a4d-5b59cced0f8c

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution : BoxSumLattice := by
  intro hBS
  obtain ⟨C₀, hC₀⟩ := hBS
  refine ⟨max |C₀| 1, le_max_right _ _, ?_⟩
  intro E _ _ _ aa L x K Θ a haa hL hx hK ha hΘ hprod
  have hΘpos : 0 < Θ := by linarith
  have hapos : 0 < a := by linarith
  have hC1 : 0 < max |C₀| 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hwl : ∀ (w : InfinitePlace E) (l : E), 0 ≤ w l := by
    intro w l
    first
    | exact w.nonneg l
    | exact apply_nonneg w l
    | exact w.1.nonneg l
  have hfac : ∀ (z : InfinitePlace E → ℝ) (l : E) (w : InfinitePlace E), 0 ≤ z w →
      0 ≤ min 1 ((z w / w l) ^ K) := fun z l w hz =>
    le_min zero_le_one (pow_nonneg (div_nonneg hz (hwl w l)) K)
  have hnonneg : ∀ l, 0 ≤ prof x K l := by
    intro l
    simp only [prof]
    exact Finset.prod_nonneg (fun w _ => hfac x l w (hx w))
  have hZpos : 0 < a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
    have h1 : 0 < a ^ ((K : ℝ) - 5 / 2) := Real.rpow_pos_of_pos hapos _
    have h2 : 0 < Θ ^ (-((K : ℝ) - 5 / 2)) := Real.rpow_pos_of_pos hΘpos _
    exact mul_pos h1 h2
  have hep : 0 ≤ (max |C₀| 1 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^
      Fintype.card (InfinitePlace E) := by
    rw [mul_assoc]
    exact pow_nonneg (mul_pos hC1 hZpos).le _
  unfold TA.LatSum
  refine ⟨hnonneg, ?_⟩
  intro S hS
  by_cases hz : ∃ w, x w = 0
  · obtain ⟨w₀, hw₀⟩ := hz
    have h0 : ∀ l, prof x K l = 0 := by
      intro l
      simp only [prof]
      apply Finset.prod_eq_zero (Finset.mem_univ w₀)
      rw [hw₀, zero_div, zero_pow (by omega)]
      exact min_eq_right zero_le_one
    simp only [h0, Finset.sum_const_zero]
    exact hep
  push_neg at hz
  have hxpos : ∀ w, 0 < x w := fun w => lt_of_le_of_ne (hx w) (hz w).symm
  have hn0 : Fintype.card (InfinitePlace E) ≠ 0 := Fintype.card_ne_zero
  have hPpos : 0 < ∏ w, x w := Finset.prod_pos (fun w _ => hxpos w)
  have haΘ : 0 < (a / Θ) ^ Fintype.card (InfinitePlace E) := pow_pos (div_pos hapos hΘpos) _
  have hNpos : 0 < √(FractionalIdeal.absNorm aa : ℝ) := by
    by_contra hcon
    push_neg at hcon
    nlinarith [haΘ, hPpos, hprod, hcon]
  set n := Fintype.card (InfinitePlace E) with hn
  set P := ∏ w, x w with hP
  set N := √(FractionalIdeal.absNorm aa : ℝ) with hN
  set T := (a / Θ) ^ n * N with hT
  have hTpos : 0 < T := mul_pos haΘ hNpos
  set lam := (T / P) ^ ((n : ℝ)⁻¹) with hlam
  have hlam1 : 1 ≤ lam := Real.one_le_rpow ((one_le_div hPpos).mpr hprod) (by positivity)
  have hlamn : lam ^ n = T / P := Real.rpow_inv_natCast_pow (div_pos hTpos hPpos).le hn0
  set y : InfinitePlace E → ℝ := fun w => lam * x w with hy
  have hypos : ∀ w, 0 < y w := fun w => mul_pos (by linarith) (hxpos w)
  have hxy : ∀ w, x w ≤ y w := fun w => le_mul_of_one_le_left (hx w) hlam1
  have hprody : ∏ w, y w = T := by
    simp only [hy, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    rw [← hn, hlamn, ← hP, div_mul_cancel₀ _ hPpos.ne']
  have heq : (Θ / a) ^ n = N / ∏ w, y w := by
    rw [hprody, hT, mul_comm, ← div_div, div_self hNpos.ne', one_div, ← inv_pow, inv_div]
  have hS' : ∀ l ∈ S, l ∈ aa ∧ l ≠ 0 := fun l hl => ⟨hL l (hS l hl).1, (hS l hl).2⟩
  have h2 : 2 < Θ / a := by
    first
    | (rw [lt_div_iff₀ hapos]; linarith)
    | (rw [lt_div_iff hapos]; linarith)
  have h3 : (3 : ℝ) ≤ K := by exact_mod_cast hK
  have hB := hC₀ E aa haa y (Θ / a) K hypos h2 h3 heq S hS'
  have hZ : (Θ / a) ^ (-((K : ℝ) - 5 / 2)) = a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)) := by
    rw [Real.div_rpow hΘpos.le hapos.le, Real.rpow_neg hapos.le, div_inv_eq_mul, mul_comm]
  calc ∑ l ∈ S, prof x K l
      ≤ ∑ l ∈ S, ∏ w, min 1 ((y w / w l) ^ (K : ℝ)) := by
        apply Finset.sum_le_sum
        intro l _
        simp only [prof]
        apply Finset.prod_le_prod (fun w _ => hfac x l w (hx w))
        intro w _
        rw [Real.rpow_natCast]
        apply min_le_min_left
        have hd : x w / w l ≤ y w / w l := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hxy w) (inv_nonneg.mpr (hwl w l))
        have hd0 : 0 ≤ x w / w l := div_nonneg (hx w) (hwl w l)
        first
        | exact pow_le_pow_left hd0 hd K
        | exact pow_le_pow_left₀ hd0 hd K
    _ ≤ (C₀ * (Θ / a) ^ (-((K : ℝ) - 5 / 2))) ^ n := hB
    _ ≤ (max |C₀| 1 * a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ^ n := by
        rw [hZ, mul_assoc (max |C₀| 1)]
        have hle : |C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) ≤
            max |C₀| 1 * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hZpos.le
        have h0 : 0 ≤ |C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2))) :=
          mul_nonneg (abs_nonneg _) hZpos.le
        calc (C₀ * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n
            ≤ |(C₀ * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n| := le_abs_self _
          _ = (|C₀| * (a ^ ((K : ℝ) - 5 / 2) * Θ ^ (-((K : ℝ) - 5 / 2)))) ^ n := by
              rw [abs_pow, abs_mul, abs_of_pos hZpos]
          _ ≤ _ := by
              first
              | exact pow_le_pow_left h0 hle n
              | exact pow_le_pow_left₀ h0 hle n
end Formalism.FourierDecayAlt.P.Jx2
