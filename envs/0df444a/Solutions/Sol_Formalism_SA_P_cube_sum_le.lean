-- Prove2me | solution 1 for Formalism.SA.P.cube_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:27.968457+00:00
-- url     : https://prove2.me/submissions/5f88c065-e2b8-4e04-93b3-49791bf5ac39

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd
import Theorems.Thm_Formalism_SA_P_absNorm_pos
import Theorems.Thm_Formalism_SA_P_card_box_le
import Theorems.Thm_Formalism_SA_P_nat_log_floor_upper
import Theorems.Thm_Formalism_SA_P_min_one_inv_le
import Theorems.Thm_Formalism_SA_P_geom_prod_sum

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
theorem _root_.solution (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0)
    (x : InfinitePlace E → ℝ) (hx : ∀ w, 0 < x w) (S : Finset E) (hS : ∀ l ∈ S, l ∈ b ∧ l ≠ 0) :
    ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 ≤
      (800 : ℝ) ^ Fintype.card (InfinitePlace E) * (∏ w, x w) ^ 2 /
        (FractionalIdeal.absNorm b : ℝ) := by
  classical
  set d := Fintype.card (InfinitePlace E) with hd
  have hN : (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := absNorm_pos b hb
  set Q : ℝ := (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  let kf : E → InfinitePlace E → ℕ := fun l w => Nat.log 2 ⌊w l / x w⌋₊
  let G : (InfinitePlace E → ℕ) → ℝ := fun k => ∏ w, (1 / 2 : ℝ) ^ (k w)
  have hG0 : ∀ k, 0 ≤ G k := fun k => Finset.prod_nonneg fun _ _ => by positivity
  have hfac : ∀ (n : ℕ) (y : ℝ),
      (2 ^ (n + 1) * y) ^ 2 * ((1 / 2 : ℝ) ^ n) ^ 3 = 4 * y ^ 2 * (1 / 2) ^ n := by
    intro n y
    rw [one_div_pow, pow_succ]
    have : (0 : ℝ) < 2 ^ n := by positivity
    field_simp
    ring
  have hmin : ∀ l ∈ S, ∀ w, min 1 (x w / w l) ≤ (1 / 2 : ℝ) ^ (kf l w) := by
    intro l hl w
    have hwl : 0 < w l := NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have h := min_one_inv_le (w l / x w) (div_pos hwl (hx w))
    rwa [one_div_div] at h
  have hbox : ∀ l ∈ S, ∀ w, w l < 2 ^ (kf l w + 1) * x w := by
    intro l hl w
    have hwl : 0 < w l := NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    have h := nat_log_floor_upper (w l / x w) (div_pos hwl (hx w)).le
    rwa [div_lt_iff₀ (hx w)] at h
  have hF : ∀ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3 ≤ G (kf l) ^ 3 := by
    intro l hl
    have hwl : ∀ w : InfinitePlace E, 0 < w l :=
      fun w => NumberField.InfinitePlace.pos_iff.mpr (hS l hl).2
    apply pow_le_pow_left₀
      (Finset.prod_nonneg fun w _ => le_min zero_le_one (div_pos (hx w) (hwl w)).le)
    exact Finset.prod_le_prod (fun w _ => le_min zero_le_one (div_pos (hx w) (hwl w)).le)
      (fun w _ => hmin l hl w)
  have hfiber : ∀ k ∈ S.image kf,
      ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3 ≤ 4 ^ d * 100 ^ d * Q * G k := by
    intro k _
    have hcard := card_box_le b hb (fun w => 2 ^ (k w + 1) * x w)
      (fun w => by have := hx w; positivity) (S.filter fun l => kf l = k) (by
        intro l hl
        rw [Finset.mem_filter] at hl
        obtain ⟨hlS, hk⟩ := hl
        refine ⟨(hS l hlS).1, (hS l hlS).2, fun w => ?_⟩
        rw [← hk]
        exact hbox l hlS w)
    have e : (∏ w, (2 ^ (k w + 1) * x w) ^ 2) * G k ^ 3 = 4 ^ d * (∏ w, x w) ^ 2 * G k := by
      simp only [G]
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      simp only [hfac]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← hd, Finset.prod_pow]
    calc ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3
        ≤ ∑ l ∈ S with kf l = k, G k ^ 3 := by
          apply Finset.sum_le_sum
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [← hl.2]
          exact hF l hl.1
      _ = ((S.filter fun l => kf l = k).card : ℝ) * G k ^ 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (100 ^ d * (∏ w, (2 ^ (k w + 1) * x w) ^ 2) / (FractionalIdeal.absNorm b : ℝ)) * G k ^ 3 :=
          mul_le_mul_of_nonneg_right hcard (pow_nonneg (hG0 k) 3)
      _ = 100 ^ d * ((∏ w, (2 ^ (k w + 1) * x w) ^ 2) * G k ^ 3) / (FractionalIdeal.absNorm b : ℝ) := by
          ring
      _ = 4 ^ d * 100 ^ d * Q * G k := by
          rw [e, hQ]
          ring
  calc ∑ l ∈ S, (∏ w, min 1 (x w / w l)) ^ 3
      = ∑ k ∈ S.image kf, ∑ l ∈ S with kf l = k, (∏ w, min 1 (x w / w l)) ^ 3 :=
        (Finset.sum_fiberwise_of_maps_to (fun l hl => Finset.mem_image_of_mem kf hl) _).symm
    _ ≤ ∑ k ∈ S.image kf, 4 ^ d * 100 ^ d * Q * G k := Finset.sum_le_sum hfiber
    _ = 4 ^ d * 100 ^ d * Q * ∑ k ∈ S.image kf, G k := by rw [Finset.mul_sum]
    _ ≤ 4 ^ d * 100 ^ d * Q * 2 ^ d :=
        mul_le_mul_of_nonneg_left (geom_prod_sum _) (mul_nonneg (by positivity) hQ0)
    _ = 800 ^ d * (∏ w, x w) ^ 2 / (FractionalIdeal.absNorm b : ℝ) := by
        rw [hQ, show (800 : ℝ) = 4 * 100 * 2 by norm_num, mul_pow, mul_pow]
        ring
end Formalism.SA.P
