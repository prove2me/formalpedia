-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.feedback_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:54.940679+00:00
-- url     : https://prove2.me/submissions/e234e3b0-9013-479d-bcd1-3651a5a53b79

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_nonneg
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_lambda_lt_one
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_A_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_g_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_d_pos
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_residual_eq_common
import Theorems.Thm_FD1D_V5_LocalBellman_Normalized_rateIncrement_eq_common
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
private theorem feedback_bracket_bound
    {s r ρ : ℝ}
    (hs : 0 < s) (hr : r ≤ 1 / 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA8 : 8 ≤ A s ρ) :
    r * s + 13 * s ^ 2 / (2 * A s ρ) ≤
      bracket s r ρ (8 * s / A s ρ) := by
  have hApos := A_pos hs hρ0 hρ1
  have hAle : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have hsHalf : 0 < s + 1 / 2 := by linarith
  have hratio : s ^ 2 / (s + 1 / 2) ≤ s := by
    apply (div_le_iff₀ hsHalf).2
    nlinarith
  have hslack : 0 ≤ 1 / 2 - r := by linarith
  have hdiscard :
      -(1 / 2 - r) * s ^ 2 / (s + 1 / 2) ≥
        -(1 / 2 - r) * s := by
    have hmul := mul_le_mul_of_nonneg_left hratio hslack
    calc
      -(1 / 2 - r) * s = -((1 / 2 - r) * s) := by ring
      _ ≤ -((1 / 2 - r) * (s ^ 2 / (s + 1 / 2))) :=
        neg_le_neg hmul
      _ = -(1 / 2 - r) * s ^ 2 / (s + 1 / 2) := by ring
  have hfirst :
      r * s + 7 * s ^ 2 / A s ρ + 8 * s ^ 2 / A s ρ ^ 2 -
          s / 2 - s / (2 * A s ρ) ≤
        bracket s r ρ (8 * s / A s ρ) := by
    unfold bracket J
    calc
      r * s + 7 * s ^ 2 / A s ρ + 8 * s ^ 2 / A s ρ ^ 2 -
          s / 2 - s / (2 * A s ρ)
          ≤ s * (8 * s / A s ρ) -
              ((s - 8 * s / A s ρ) / A s ρ) * (s + 1 / 2) -
              (1 / 2 - r) * s := by
                have hfour : 0 ≤ 4 * s / A s ρ ^ 2 := by positivity
                have hid :
                    s * (8 * s / A s ρ) -
                        ((s - 8 * s / A s ρ) / A s ρ) *
                          (s + 1 / 2) -
                        (1 / 2 - r) * s =
                      r * s + 7 * s ^ 2 / A s ρ +
                        8 * s ^ 2 / A s ρ ^ 2 - s / 2 -
                        s / (2 * A s ρ) +
                        4 * s / A s ρ ^ 2 := by
                  field_simp [hApos.ne']
                  ring
                rw [hid]
                linarith
      _ ≤ s * (8 * s / A s ρ) -
              ((s - 8 * s / A s ρ) / A s ρ) * (s + 1 / 2) -
              (1 / 2 - r) * s ^ 2 / (s + 1 / 2) := by
                convert add_le_add_left hdiscard
                  (s * (8 * s / A s ρ) -
                    ((s - 8 * s / A s ρ) / A s ρ) *
                      (s + 1 / 2)) using 1 <;> ring
  have hone :
      s / 2 ≤ s ^ 2 / (2 * A s ρ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * A s ρ)).2
    nlinarith
  have htwo :
      s / (2 * A s ρ) ≤ 8 * s ^ 2 / A s ρ ^ 2 := by
    have hleft : 0 ≤ s / (2 * A s ρ) := by positivity
    have hfac : 1 ≤ 16 * s / A s ρ := by
      apply (le_div_iff₀ hApos).2
      nlinarith
    calc
      s / (2 * A s ρ) =
          (s / (2 * A s ρ)) * 1 := by ring
      _ ≤ (s / (2 * A s ρ)) * (16 * s / A s ρ) :=
        mul_le_mul_of_nonneg_left hfac hleft
      _ = 8 * s ^ 2 / A s ρ ^ 2 := by ring
  have hcombine :=
    add_le_add hone htwo
  have hbudget :
      r * s + 13 * s ^ 2 / (2 * A s ρ) +
          (s / 2 + s / (2 * A s ρ)) ≤
        r * s + 7 * s ^ 2 / A s ρ +
          8 * s ^ 2 / A s ρ ^ 2 := by
    calc
      r * s + 13 * s ^ 2 / (2 * A s ρ) +
          (s / 2 + s / (2 * A s ρ))
          = (s / 2 + s / (2 * A s ρ)) +
              (r * s + 13 * s ^ 2 / (2 * A s ρ)) := by ring
      _ ≤ (s ^ 2 / (2 * A s ρ) +
              8 * s ^ 2 / A s ρ ^ 2) +
            (r * s + 13 * s ^ 2 / (2 * A s ρ)) :=
        add_le_add_left hcombine _
      _ = r * s + 7 * s ^ 2 / A s ρ +
            8 * s ^ 2 / A s ρ ^ 2 := by ring
  calc
    r * s + 13 * s ^ 2 / (2 * A s ρ)
        ≤ r * s + 7 * s ^ 2 / A s ρ +
            8 * s ^ 2 / A s ρ ^ 2 - s / 2 -
              s / (2 * A s ρ) := by
          linarith
    _ ≤ bracket s r ρ (8 * s / A s ρ) := hfirst
private theorem feedback_delta_bounds
    {s ρ : ℝ}
    (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA8 : 8 ≤ A s ρ) :
    let α := 1 / A s ρ
    let δ := d s ρ / (s * A s ρ)
    0 ≤ α ∧ α ≤ 1 / 8 ∧
      1 + 2 * α ≤ δ ∧ δ ≤ (1 + α) ^ 2 := by
  dsimp
  have hApos := A_pos hs hρ0 hρ1
  have hAle : A s ρ ≤ s := by
    unfold A lambda
    nlinarith [sq_nonneg ρ]
  have halpha0 : 0 ≤ 1 / A s ρ := by positivity
  have halpha8 : 1 / A s ρ ≤ 1 / 8 := by
    exact one_div_le_one_div_of_le (by norm_num) hA8
  have hsA : 0 < s * A s ρ := mul_pos hs hApos
  have hdelta :
      d s ρ / (s * A s ρ) =
        1 + 2 / A s ρ + 1 / (s * A s ρ) := by
    unfold d
    field_simp [hs.ne', hApos.ne']
  rw [hdelta]
  refine ⟨halpha0, halpha8, ?_, ?_⟩
  · have : 0 ≤ 1 / (s * A s ρ) := by positivity
    calc
      1 + 2 * (1 / A s ρ) = 1 + 2 / A s ρ := by ring
      _ ≤ 1 + 2 / A s ρ + 1 / (s * A s ρ) :=
        le_add_of_nonneg_right this
  · have hone : 1 / s ≤ 1 / A s ρ :=
      one_div_le_one_div_of_le hApos hAle
    have hmul :
        1 / (s * A s ρ) ≤ 1 / A s ρ ^ 2 := by
      calc
        1 / (s * A s ρ) = (1 / s) * (1 / A s ρ) := by
          field_simp
        _ ≤ (1 / A s ρ) * (1 / A s ρ) :=
          mul_le_mul_of_nonneg_right hone halpha0
        _ = 1 / A s ρ ^ 2 := by ring
    calc
      1 + 2 / A s ρ + 1 / (s * A s ρ)
          ≤ 1 + 2 / A s ρ + 1 / A s ρ ^ 2 := by
            linarith
      _ = (1 + 1 / A s ρ) ^ 2 := by ring
private theorem feedback_fraction_bound
    {α δ lam : ℝ}
    (hα0 : 0 ≤ α) (hα8 : α ≤ 1 / 8)
    (hδ : 1 + 2 * α ≤ δ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α)) ≤
      19 / 8 := by
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ
  have hδplus : 0 < δ + 8 * lam * α := by positivity
  have hlamDiff : 0 ≤ (1 - lam) * (1 + 2 * α) := by positivity
  have hsecond :
      lam * (1 + 10 * α) ≤ δ + 8 * lam * α := by
    nlinarith
  have hcross :
      lam * ((1 + 2 * α) * (1 + 10 * α)) ≤
        δ * (δ + 8 * lam * α) := by
    calc
      lam * ((1 + 2 * α) * (1 + 10 * α)) =
          (1 + 2 * α) * (lam * (1 + 10 * α)) := by ring
      _ ≤ δ * (δ + 8 * lam * α) :=
        mul_le_mul hδ hsecond (by positivity) hδpos.le
  have hcoarse :
      2 * (1 + (13 / 2) * α) ^ 2 /
          ((1 + 2 * α) * (1 + 10 * α)) ≤
        19 / 8 := by
    have hden0 : 0 < (1 + 2 * α) * (1 + 10 * α) := by positivity
    apply (div_le_iff₀ hden0).2
    have hpoly : 0 ≤ 3 / 8 + 5 / 2 * α - 37 * α ^ 2 := by
      have haux : 37 * α ^ 2 ≤ 37 / 8 * α := by
        nlinarith [mul_nonneg hα0 (sub_nonneg.mpr hα8)]
      nlinarith
    nlinarith
  calc
    2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α))
        ≤ 2 * (1 + (13 / 2) * α) ^ 2 /
          ((1 + 2 * α) * (1 + 10 * α)) := by
        apply (div_le_div_iff₀
          (mul_pos hδpos hδplus) (by positivity)).2
        have hfactor : 0 ≤ 2 * (1 + (13 / 2) * α) ^ 2 := by positivity
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hcross hfactor
    _ ≤ 19 / 8 := hcoarse
private theorem feedback_quadratic_bound
    {u α δ lam : ℝ}
    (hα0 : 0 ≤ α) (hα8 : α ≤ 1 / 8)
    (hδLower : 1 + 2 * α ≤ δ)
    (hδUpper : δ ≤ (1 + α) ^ 2)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    lam / 12 ≤
      u ^ 2 / 8 +
        lam / δ * (1 + α * u) * (u + 13 / 2) -
        8 / 3 * lam := by
  have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδLower
  have hlead : 0 < δ + 8 * lam * α := by positivity
  have hfrac :=
    feedback_fraction_bound hα0 hα8 hδLower hlam0 hlam1
  have hdelta81 : δ ≤ 81 / 64 := by
    calc
      δ ≤ (1 + α) ^ 2 := hδUpper
      _ ≤ (1 + (1 / 8 : ℝ)) ^ 2 := by gcongr
      _ = 81 / 64 := by norm_num
  have hC : 41 / 8 ≤ (13 / 2 : ℝ) / δ := by
    apply (le_div_iff₀ hδpos).2
    nlinarith
  have hsquare :
      0 ≤
        (δ + 8 * lam * α) *
          (u + 4 * lam * (1 + (13 / 2) * α) /
            (δ + 8 * lam * α)) ^ 2 / (8 * δ) := by
    positivity
  have hid :
      u ^ 2 / 8 +
          lam / δ * (1 + α * u) * (u + 13 / 2) -
          8 / 3 * lam =
        (δ + 8 * lam * α) *
            (u + 4 * lam * (1 + (13 / 2) * α) /
              (δ + 8 * lam * α)) ^ 2 / (8 * δ) +
          lam * ((13 / 2 : ℝ) / δ - 8 / 3 -
            2 * lam * (1 + (13 / 2) * α) ^ 2 /
              (δ * (δ + 8 * lam * α))) := by
    field_simp [hδpos.ne', hlead.ne']
    ring
  rw [hid]
  have hbracket :
      1 / 12 ≤ (13 / 2 : ℝ) / δ - 8 / 3 -
        2 * lam * (1 + (13 / 2) * α) ^ 2 /
          (δ * (δ + 8 * lam * α)) := by
    nlinarith
  have := mul_le_mul_of_nonneg_left hbracket hlam0
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
set_option maxHeartbeats 800000
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution
    {s r ρ : ℝ}
    (hs : 0 < s) (hr0 : -s < r) (hr1 : r ≤ 1 / 2)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hactive : feedback s ρ ≤ uniform s ρ) :
    residual s r ρ (feedback s ρ) ≥
      (rateIncrement s ρ (feedback s ρ) + feedback s ρ ^ 2) / 1000 := by
  have hρnonneg : 0 ≤ ρ := hρ0.le
  have hlam0 : 0 ≤ lambda ρ := lambda_nonneg ρ
  have hlam1 : lambda ρ ≤ 1 := (lambda_lt_one hρnonneg hρ1).le
  have hApos := A_pos hs hρnonneg hρ1
  have hA8 : 8 ≤ A s ρ := by
    unfold feedback uniform at hactive
    have hsρ : 0 < s * ρ := mul_pos hs hρ0
    have hmul := (div_le_iff₀ hApos).1 hactive
    nlinarith
  let ω : ℝ := s / A s ρ
  let α : ℝ := 1 / A s ρ
  let u : ℝ := r / ω
  let δ : ℝ := d s ρ / (s * A s ρ)
  have hωpos : 0 < ω := div_pos hs hApos
  have hωone : 1 ≤ ω := by
    have hAle : A s ρ ≤ s := by
      unfold A lambda
      nlinarith [sq_nonneg ρ]
    exact (le_div_iff₀ hApos).2 (by simpa using hAle)
  obtain ⟨hα0, hα8, hδLower, hδUpper⟩ :=
    feedback_delta_bounds hs hρnonneg hρ1 hA8
  have hquad :=
    feedback_quadratic_bound
      (u := u) hα0 hα8 hδLower hδUpper hlam0 hlam1
  have hg : 0 < g s r := g_pos hr0
  have hthird :
      0 ≤ g s r * (1 / 2 - r) * (s + 1) /
        (2 * d s ρ * (s + 1 / 2)) := by
    have hdpos := d_pos hs hρnonneg hρ1
    positivity
  have hbracket :=
    feedback_bracket_bound hs hr1 hρnonneg hρ1 hA8
  have hcommon :=
    residual_eq_common
      (s := s) (r := r) (ρ := ρ) (k := 8 * s / A s ρ)
      hs hρnonneg hρ1
  have hfeedback :
      feedback s ρ = ρ * (8 * s / A s ρ) := by
    unfold feedback
    ring
  have hnormalize :
      ω ^ 2 *
          (u ^ 2 / 8 +
            lambda ρ / δ * (1 + α * u) * (u + 13 / 2) -
            8 / 3 * lambda ρ) =
        r ^ 2 / 8 - lambda ρ * (8 * s / A s ρ) ^ 2 / 24 +
          lambda ρ * g s r / d s ρ *
            (r * s + 13 * s ^ 2 / (2 * A s ρ)) := by
    dsimp [ω, α, u, δ]
    have hdpos := d_pos hs hρnonneg hρ1
    field_simp [hs.ne', hApos.ne', hdpos.ne']
    unfold g
    ring
  have hres :
      lambda ρ * ω ^ 2 / 12 ≤
        residual s r ρ (feedback s ρ) := by
    rw [hfeedback, hcommon]
    have hquadScaled :=
      mul_le_mul_of_nonneg_left hquad (sq_nonneg ω)
    rw [hnormalize] at hquadScaled
    have hlast :
        lambda ρ * g s r / d s ρ *
              (r * s + 13 * s ^ 2 / (2 * A s ρ)) ≤
          lambda ρ * g s r / d s ρ *
              bracket s r ρ (8 * s / A s ρ) := by
      have hcoef :
          0 ≤ lambda ρ * g s r / d s ρ :=
        div_nonneg (mul_nonneg hlam0 hg.le)
          (d_pos hs hρnonneg hρ1).le
      exact mul_le_mul_of_nonneg_left hbracket hcoef
    nlinarith
  have hJ :
      J s ρ (8 * s / A s ρ) =
        ω * (1 - 8 / A s ρ) := by
    dsimp [ω]
    unfold J
    field_simp [hApos.ne']
  have hJ0 : 0 ≤ J s ρ (8 * s / A s ρ) := by
    rw [hJ]
    have hfrac : 8 / A s ρ ≤ 1 :=
      (div_le_one hApos).2 hA8
    exact mul_nonneg hωpos.le (sub_nonneg.mpr hfrac)
  have hJω : J s ρ (8 * s / A s ρ) ≤ ω := by
    rw [hJ]
    have : 0 ≤ 8 / A s ρ := by positivity
    nlinarith
  have hrateCommon :=
    rateIncrement_eq_common
      (s := s) (ρ := ρ) (k := 8 * s / A s ρ)
      hs hρnonneg hρ1
  have hfeedbackSq :
      feedback s ρ ^ 2 = 64 * lambda ρ * ω ^ 2 := by
    dsimp [ω]
    unfold feedback lambda
    ring
  have hrate :
      rateIncrement s ρ (feedback s ρ) ≤
        4 * lambda ρ * ω ^ 2 := by
    rw [hfeedback, hrateCommon]
    have hlinear :
        2 * lambda ρ * J s ρ (8 * s / A s ρ) ≤
          2 * lambda ρ * ω ^ 2 := by
      have hJone :
          J s ρ (8 * s / A s ρ) ≤ ω ^ 2 :=
        hJω.trans (by nlinarith [hωone])
      exact mul_le_mul_of_nonneg_left hJone (by positivity)
    have hquadJ :
        (1 + lambda ρ) * lambda ρ *
            J s ρ (8 * s / A s ρ) ^ 2 ≤
          2 * lambda ρ * ω ^ 2 := by
      have hJsq :
          J s ρ (8 * s / A s ρ) ^ 2 ≤ ω ^ 2 :=
        (sq_le_sq₀ hJ0 hωpos.le).2 hJω
      have honeLambda : 1 + lambda ρ ≤ 2 := by linarith
      calc
        (1 + lambda ρ) * lambda ρ *
              J s ρ (8 * s / A s ρ) ^ 2
            ≤ 2 * lambda ρ *
              J s ρ (8 * s / A s ρ) ^ 2 := by
                gcongr
        _ ≤ 2 * lambda ρ * ω ^ 2 := by
          exact mul_le_mul_of_nonneg_left hJsq (by positivity)
    exact (add_le_add hlinear hquadJ).trans_eq (by ring)
  have htarget :
      (rateIncrement s ρ (feedback s ρ) + feedback s ρ ^ 2) / 1000 ≤
        lambda ρ * ω ^ 2 / 12 := by
    rw [hfeedbackSq]
    have henergyNonneg : 0 ≤ lambda ρ * ω ^ 2 := by positivity
    nlinarith
  exact htarget.trans hres
end FD1D.V5.LocalBellman.Normalized
