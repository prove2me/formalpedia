-- Prove2me | solution 1 for Formalism.ZF.ldr_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:31.244207+00:00
-- url     : https://prove2.me/submissions/8ca0d8b0-4099-4f84-9339-68a33612a2cf

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrInvSubOneLe
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LdrMid
import Theorems.Thm_Formalism_ZF_ldr_inv_sub_one_le
import Theorems.Thm_Formalism_ZF_zfo_M_bound
import Theorems.Thm_Formalism_ZF_zfo_diff_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by
  set T := |t| with hTdef
  set L := Real.log (T + 2) with hLdef
  have hLpos : 0 < L := by linarith
  have hT0 : 0 ≤ T := abs_nonneg t
  have hLX : L ≤ T + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith)
    linarith
  have hT3 : 3 ≤ T := by linarith
  set u := 1 / L with hudef
  have hu : 0 < u := by positivity
  have hu24 : u ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) hL
  have hLu : L * u = 1 := by rw [hudef]; field_simp
  set σ₀ := 1 + u with hσ₀def
  have hσ₀1 : 1 < σ₀ := by linarith
  have hσ₀2 : σ₀ ≤ 2 := by linarith
  have hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2) := by
    have e : 2 / (σ₀ - 1) = 2 * L := by
      rw [show σ₀ - 1 = u by ring, hudef, div_div_eq_mul_div, div_one]
    rw [e]; linarith
  set z₀ : ℂ := (σ₀ : ℂ) + t * I with hz₀
  have hz0re : z₀.re = σ₀ := by simp [z₀]
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; exact hσ₀1)
  have hM := zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith)
  have hM1 : 1 ≤ (T + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨Z, m, hZ, hm, hsum, hder⟩ :=
    hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num) hM1 (zfo_diff_ball hT3) hz0 hM
  have hlogM : Real.log ((T + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogM] at hsum hder
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsz : s - z₀ = ((σ - σ₀ : ℝ) : ℂ) := by
    simp only [s, z₀, Complex.ofReal_sub]; ring
  have hs_mem : s ∈ closedBall z₀ (1 / 2 / 6) := by
    rw [mem_closedBall, dist_eq_norm, hsz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at hTdef; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; exact ht0 this
  have hc4 : (c₀ / 4) / L ≤ c₀ / L := div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hs_ne : riemannZeta s ≠ 0 := by
    apply hZ0 s hs1
    rw [hsre, hsim]; linarith
  have hD := hder s hs_mem hs_ne

  set δ := (c₀ / 4) / L with hδdef
  have hδ : 0 < δ := by positivity
  have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ := by
    intro ρ hρ
    obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
    rw [mem_closedBall, dist_eq_norm] at hρb
    have him : |ρ.im - t| ≤ 1 / 6 := by
      have h1 : (ρ - z₀).im = ρ.im - t := by simp [z₀]
      rw [← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)
    have hρim : |ρ.im| ≤ T + 1 / 6 := by
      have := abs_sub_abs_le_abs_sub ρ.im t; linarith
    have hρim' : T - 1 / 6 ≤ |ρ.im| := by
      have := abs_sub_abs_le_abs_sub t ρ.im; rw [abs_sub_comm] at this; linarith
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at hρim'; linarith
    have hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2) := by
      by_contra hc; exact hZ0 ρ hρ1 (not_lt.mp hc) hρ0
    have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      have e : 2 * L = Real.log ((T + 2) ^ 2) := by rw [Real.log_pow]; push_cast; ring
      rw [e]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hlogρpos : 0 < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have h2 : c₀ / (2 * L) ≤ c₀ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₀.le hlogρpos hlogρ
    have h3 : c₀ / (2 * L) = 2 * δ := by rw [hδdef]; field_simp; ring
    have hsρ : δ < (s - ρ).re := by rw [Complex.sub_re, hsre]; linarith
    have hn : δ < ‖s - ρ‖ := lt_of_lt_of_le hsρ (Complex.re_le_norm _)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le
  have hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2 := by
    have h1 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have h2 : ∑ ρ ∈ Z, (m ρ : ℝ) / δ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
      rw [← Finset.sum_div]; push_cast; rfl
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2pos : 0 < Real.log 2 := by linarith
    have h3 : 10 * L / Real.log 2 ≤ 15 * L := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have h4 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ ≤ 15 * L / δ :=
      div_le_div_of_nonneg_right (hsum.trans h3) hδ.le
    have h5 : 15 * L / δ = (60 / c₀) * L ^ 2 := by rw [hδdef]; field_simp; ring
    linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := ldr_inv_sub_one_le (by rw [hsim]; linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1) := by ring
  have hD' : (72 : ℝ) * (10 * L) / (1 / 2) = 1440 * L := by ring
  rw [hD'] at hD
  have htot : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 1440 * L + (60 / c₀) * L ^ 2 + 1 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hLL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith
end Formalism.ZF
