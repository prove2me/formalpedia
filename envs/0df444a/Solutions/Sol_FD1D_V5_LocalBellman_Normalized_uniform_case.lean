-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.uniform_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:54.411909+00:00
-- url     : https://prove2.me/submissions/a07e1c49-87b4-4054-add0-a5475bc18fa7

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_nonneg
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_g_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_d_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_rateIncrement
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_uniform_residual_eq
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
private theorem denominator_ratio_identity
    {s ρ : ℝ} (hs : s ≠ 0) :
    d s ρ * (s + 1 / 2) / s ^ 2 =
      A s ρ + 2 + A s ρ / (2 * s) + 2 / s +
        1 / (2 * s ^ 2) := by
  unfold d
  field_simp
  ring
private theorem uniform_denominator_le
    {s ρ : ℝ}
    (hs : 1 / 2 ≤ s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hactive : A s ρ ≤ 8) :
    d s ρ * (s + 1 / 2) ≤ 13 * s ^ 2 := by
  have hspos : 0 < s := by linarith
  have hA0 : 0 ≤ A s ρ := (A_pos hspos hρ0 hρ1).le
  have hAleS : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have hid := denominator_ratio_identity (ρ := ρ) hspos.ne'
  by_cases hs1 : s ≤ 1
  · have hA : A s ρ ≤ 1 := hAleS.trans hs1
    have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
      linarith
    have h2div : 2 / s ≤ 4 := by
      apply (div_le_iff₀ hspos).2
      nlinarith
    have hlast : 1 / (2 * s ^ 2) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
      nlinarith [sq_nonneg (s - 1 / 2)]
    have hratio :
        d s ρ * (s + 1 / 2) / s ^ 2 ≤ 19 / 2 := by
      rw [hid]
      linarith
    have hsSq : 0 < s ^ 2 := sq_pos_of_pos hspos
    have := (div_le_iff₀ hsSq).1 hratio
    nlinarith
  · have hsone : 1 ≤ s := le_of_not_ge hs1
    by_cases hs8 : s ≤ 8
    · have hA : A s ρ ≤ 8 := hactive
      have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
        linarith
      have h2div : 2 / s ≤ 2 := by
        apply (div_le_iff₀ hspos).2
        nlinarith
      have hlast : 1 / (2 * s ^ 2) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
        nlinarith [sq_nonneg (s - 1)]
      have hratio :
          d s ρ * (s + 1 / 2) / s ^ 2 ≤ 13 := by
        rw [hid]
        linarith
      exact (div_le_iff₀ (sq_pos_of_pos hspos)).1 hratio
    · have hsEight : 8 ≤ s := le_of_not_ge hs8
      have hA : A s ρ ≤ 8 := hactive
      have hAdiv : A s ρ / (2 * s) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
        nlinarith [hAleS]
      have h2div : 2 / s ≤ 1 / 4 := by
        apply (div_le_iff₀ hspos).2
        nlinarith
      have hlast : 1 / (2 * s ^ 2) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * s ^ 2)).2
        nlinarith [sq_nonneg (s - 1)]
      have hratio :
          d s ρ * (s + 1 / 2) / s ^ 2 ≤ 13 := by
        rw [hid]
        linarith
      exact (div_le_iff₀ (sq_pos_of_pos hspos)).1 hratio
private theorem weighted_square_bound
    {s r lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam * s ^ 2 / 21 ≤ r ^ 2 / 8 + lam * (s + r) ^ 2 / 13 := by
  let C : ℝ := 168 * lam + 273
  have hC : 0 < C := by dsimp [C]; nlinarith
  have hrem : 0 ≤ 69888 * lam * (1 - lam) * s ^ 2 := by positivity
  have hid :
      4 * C *
          (168 * lam * r ^ 2 + 336 * lam * r * s +
            64 * lam * s ^ 2 + 273 * r ^ 2) =
        (2 * C * r + 336 * lam * s) ^ 2 +
          69888 * lam * (1 - lam) * s ^ 2 := by
    dsimp [C]
    ring
  have hpoly :
      0 ≤ 168 * lam * r ^ 2 + 336 * lam * r * s +
        64 * lam * s ^ 2 + 273 * r ^ 2 := by
    nlinarith [sq_nonneg (2 * C * r + 336 * lam * s)]
  nlinarith
end Normalized
end
end FD1D.V5.LocalBellman
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hactive : A s ρ ≤ 8) :
    residual s r ρ (uniform s ρ) ≥
      (rateIncrement s ρ (uniform s ρ) + uniform s ρ ^ 2) / 1000 := by
  have hg : 0 < g s r := g_pos hr0
  have hlam0 : 0 ≤ lambda ρ := lambda_nonneg ρ
  have hlam1 : lambda ρ ≤ 1 := (lambda_lt_one hρ0 hρ1).le
  have hzsq : uniform s ρ ^ 2 = lambda ρ * s ^ 2 := by
    unfold uniform lambda
    ring
  rw [uniform_rateIncrement hs hρ0 hρ1, zero_add]
  rw [uniform_residual_eq hs hr0 hr1 hρ0 hρ1]
  by_cases hsHalf : 1 / 2 ≤ s
  · have hden := uniform_denominator_le hsHalf hρ0 hρ1 hactive
    have hdpos : 0 < d s ρ * (s + 1 / 2) := by
      exact mul_pos (d_pos hs hρ0 hρ1) (by linarith)
    have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
    have hsquare :
        lambda ρ * g s r ^ 2 / 13 ≤
          g s r ^ 2 * uniform s ρ ^ 2 /
            (d s ρ * (s + 1 / 2)) := by
      rw [hzsq]
      have hnum : 0 ≤ lambda ρ * g s r ^ 2 := by positivity
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 13) hdpos).2
      nlinarith
    have hcauchy :=
      weighted_square_bound (s := s) (r := r) hlam0 hlam1
    have hlast :
        0 ≤ g s r * (1 / 2 - r) * (s + 1) /
          (2 * d s ρ * (s + 1 / 2)) := by
      have hhalf : 0 ≤ 1 / 2 - r := by linarith
      have hsone : 0 ≤ s + 1 := by linarith
      have hden : 0 < 2 * d s ρ * (s + 1 / 2) :=
        mul_pos (mul_pos (by norm_num) (d_pos hs hρ0 hρ1)) (by linarith)
      exact div_nonneg
        (mul_nonneg (mul_nonneg hg.le hhalf) hsone) hden.le
    simp only [g] at hsquare hlast ⊢
    nlinarith
  · have hsUpper : s ≤ 1 / 2 := le_of_not_ge hsHalf
    have hAleS : A s ρ ≤ s := by
      unfold A lambda
      nlinarith [sq_nonneg ρ]
    have hdUpper : d s ρ ≤ (s + 1) ^ 2 := by
      unfold d
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hAleS)]
    have hcoef :
        1 / 3 ≤ (s + 1) / (2 * d s ρ * (s + 1 / 2)) := by
      have hdpos := d_pos hs hρ0 hρ1
      have hden : 0 < 2 * d s ρ * (s + 1 / 2) := by positivity
      apply (le_div_iff₀ hden).2
      have hbound :
          2 * (s + 1) ^ 2 * (s + 1 / 2) ≤ 3 * (s + 1) := by
        have hfac : 0 ≤ s + 1 := by positivity
        nlinarith [mul_nonneg hfac
          (mul_nonneg (sub_nonneg.mpr hs.le) (by linarith : 0 ≤ 1 - s))]
      nlinarith [mul_le_mul_of_nonneg_right hdUpper
        (by linarith : 0 ≤ 2 * (s + 1 / 2))]
    have hlast :
        g s r * (1 / 2 - r) / 3 ≤
          g s r * (1 / 2 - r) * (s + 1) /
            (2 * d s ρ * (s + 1 / 2)) := by
      have hfactor : 0 ≤ g s r * (1 / 2 - r) := by positivity
      calc
        g s r * (1 / 2 - r) / 3 =
            (g s r * (1 / 2 - r)) * (1 / 3) := by ring
        _ ≤ (g s r * (1 / 2 - r)) *
              ((s + 1) / (2 * d s ρ * (s + 1 / 2))) :=
          mul_le_mul_of_nonneg_left hcoef hfactor
        _ = g s r * (1 / 2 - r) * (s + 1) /
              (2 * d s ρ * (s + 1 / 2)) := by ring
    have hzle : uniform s ρ ^ 2 ≤ s ^ 2 := by
      rw [hzsq]
      nlinarith [mul_le_mul_of_nonneg_right hlam1 (sq_nonneg s)]
    have hcore :
        s ^ 2 / 12 ≤ r ^ 2 / 8 - s ^ 2 / 24 +
          (s + r) * (1 / 2 - r) / 3 := by
      have hleft : 0 ≤ r + s := by linarith
      have hright : 0 ≤ 4 - 5 * r - 3 * s := by linarith
      nlinarith [mul_nonneg hleft hright]
    have hsquare :
        0 ≤ g s r ^ 2 * uniform s ρ ^ 2 /
          (d s ρ * (s + 1 / 2)) := by
      have hden : 0 < d s ρ * (s + 1 / 2) :=
        mul_pos (d_pos hs hρ0 hρ1) (by linarith)
      exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hden.le
    simp only [g] at hlast hsquare ⊢
    nlinarith
end FD1D.V5.LocalBellman.Normalized
