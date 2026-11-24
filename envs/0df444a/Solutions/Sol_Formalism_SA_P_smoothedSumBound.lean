-- Prove2me | solution 1 for Formalism.SA.P.smoothedSumBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:42.316798+00:00
-- url     : https://prove2.me/submissions/211af26f-6651-416a-87da-8bd3fd844543

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Theorems.Thm_Formalism_SA_P_sqrt_absNorm_le_prod
import Theorems.Thm_Formalism_SA_P_absNorm_pos
import Theorems.Thm_Formalism_SA_P_cube_sum_le
import Theorems.Thm_Formalism_SA_P_min_one_rpow
import Theorems.Thm_Formalism_SA_P_pow_rpow_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution : Formalism.SA.C.BoxSum := by
  refine ⟨800, ?_⟩
  intro E _ _ _ b hb x Θ Kx hx hΘ hK hΘd S hS
  set d := Fintype.card (InfinitePlace E) with hd
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := absNorm_pos b hb
  have hΘ0 : 0 < Θ := by linarith
  set A : ℝ := Θ ^ d with hA
  have hA1 : 1 ≤ A := one_le_pow₀ (by linarith)
  have hA0 : 0 < A := by linarith
  have hpx : 0 < ∏ w, x w := Finset.prod_pos fun w _ => hx w
  have hsq : (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) = 1 / A ^ 2 := by
    rw [hΘd, div_pow, Real.sq_sqrt hN.le, one_div_div]
  have hinvA : 1 / A = (∏ w, x w) / √(FractionalIdeal.absNorm b : ℝ) := by
    rw [hΘd, one_div_div]
  have hterm : ∀ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
      (∏ w, min 1 (x w / w l)) ^ 3 * (1 / A) ^ (Kx - 3) := by
    intro l hl
    have hwl : ∀ w : InfinitePlace E, 0 < w l :=
      fun w => NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have hm0 : ∀ w, 0 ≤ min 1 (x w / w l) :=
      fun w => le_min zero_le_one (div_pos (hx w) (hwl w)).le
    have hp0 : 0 < ∏ w, min 1 (x w / w l) :=
      Finset.prod_pos fun w _ => lt_min one_pos (div_pos (hx w) (hwl w))
    have e1 : ∏ w, min 1 ((x w / w l) ^ Kx) = (∏ w, min 1 (x w / w l)) ^ Kx := by
      rw [← Real.finset_prod_rpow _ _ (fun w _ => hm0 w)]
      refine Finset.prod_congr rfl fun w _ => ?_
      exact min_one_rpow _ _ (div_pos (hx w) (hwl w)) (by linarith)
    have hpA : ∏ w, min 1 (x w / w l) ≤ 1 / A := by
      have h1 : ∏ w, min 1 (x w / w l) ≤ ∏ w, (x w / w l) :=
        Finset.prod_le_prod (fun w _ => hm0 w) (fun w _ => min_le_right _ _)
      rw [Finset.prod_div_distrib] at h1
      have h3 := sqrt_absNorm_le_prod b hb l (hS l hl).1 (hS l hl).2
      rw [hinvA]
      calc ∏ w, min 1 (x w / w l) ≤ (∏ w, x w) / ∏ w : InfinitePlace E, w l := h1
        _ ≤ (∏ w, x w) / √(FractionalIdeal.absNorm b : ℝ) :=
            div_le_div_of_nonneg_left hpx.le (Real.sqrt_pos.mpr hN) h3
    have e2 : (∏ w, min 1 (x w / w l)) ^ Kx =
        (∏ w, min 1 (x w / w l)) ^ ((3 : ℕ) : ℝ) * (∏ w, min 1 (x w / w l)) ^ (Kx - 3) := by
      rw [← Real.rpow_add hp0]
      congr 1
      push_cast
      ring
    rw [e1, e2, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp0.le hpA (by linarith)) (by positivity)
  have e : 1 / A ^ 2 * (1 / A) ^ (Kx - 3) = A ^ (-(Kx - 1)) := by
    rw [show -(Kx - 1) = (-2 : ℝ) + -(Kx - 3) by ring, Real.rpow_add hA0, Real.rpow_neg hA0.le,
      Real.rpow_neg hA0.le, one_div, one_div, Real.inv_rpow hA0.le, Real.rpow_two]
  calc ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx)
      ≤ ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 * (1 / A) ^ (Kx - 3) := Finset.sum_le_sum hterm
    _ = (∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3) * (1 / A) ^ (Kx - 3) := by rw [Finset.sum_mul]
    _ ≤ (800 ^ d * (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ)) * (1 / A) ^ (Kx - 3) :=
        mul_le_mul_of_nonneg_right (cube_sum_le b hb x hx S hS) (by positivity)
    _ = 800 ^ d * A ^ (-(Kx - 1)) := by
        rw [mul_div_assoc, hsq, mul_assoc, e]
    _ ≤ 800 ^ d * A ^ (-(Kx - 5 / 2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)) (by positivity)
    _ = (800 * Θ ^ (-(Kx - 5 / 2))) ^ d := by
        rw [mul_pow, hA, pow_rpow_comm Θ _ hΘ0]
end Formalism.SA.P
