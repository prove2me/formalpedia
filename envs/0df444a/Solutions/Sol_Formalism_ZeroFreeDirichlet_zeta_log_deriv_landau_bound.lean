-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zeta_log_deriv_landau_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:35.854025+00:00
-- url     : https://prove2.me/submissions/f471b900-2b5e-4080-bcf3-9ed479db94b2

import Definitions.Def_Formalism_ZeroFreeRegion_LogDerivRegion
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaLogDerivLandauBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_nonneg
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_re_le_norm
import Theorems.Thm_Formalism_ZF_growthBound
import Theorems.Thm_Formalism_ZF_landauLocal
import Theorems.Thm_Formalism_ZF_zetaInvBound_statement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Filter Topology
noncomputable section
namespace Formalism.ZeroFreeDirichlet
private lemma re_natCast_div_nonneg (k : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ ((k : ℂ) / w).re := by
  have e : (k : ℂ) / w = ((k : ℝ) : ℂ) * (1 / w) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg k) (re_one_div_nonneg hw)
private lemma re_ge_and_norm_zeta_le_of_near_eleven_tenths {t : ℝ} (ht : 2 < |t|) {z : ℂ}
    (hz : ‖z - (((11 / 10 : ℝ) : ℂ) + t * I)‖ ≤ 3 / 5) :
    1 / 2 ≤ z.re ∧ z ≠ 1 ∧ ‖riemannZeta z‖ ≤ 6 * (|t| + 2) := by
  have h1 := Complex.abs_re_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have h2 := Complex.abs_im_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have er : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).re = z.re - 11 / 10 := by simp
  have ei : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).im = z.im - t := by simp
  rw [er] at h1
  rw [ei] at h2
  have hre := abs_le.mp (h1.trans hz)
  have h2' := h2.trans hz
  have him1 : |t| - |z.im| ≤ |z.im - t| := by rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub t z.im
  have him2 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
  have hzre : 1 / 2 ≤ z.re := by linarith [hre.1]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at h2'
    linarith
  have hd : 1 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hzn : ‖z‖ ≤ |t| + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have hr : |z.re| ≤ 17 / 10 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
    linarith
  have hg := Formalism.ZF.growthBound z (by linarith) hz1
  have hA : 1 / ‖z - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hd
  have hB : 1 / z.re ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hC : ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 3) * 3 :=
    mul_le_mul hzn (by linarith)
      (by have := one_div_pos.mpr (by linarith : (0 : ℝ) < z.re); linarith) (by positivity)
  refine ⟨hzre, hz1, ?_⟩
  linarith
end Formalism.ZeroFreeDirichlet
end
end

set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (t σ : ℝ) (ht : 2 < |t|) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      840 * Real.log (|t| + 2) := by
  have hz0re : ((((11 / 10 : ℝ) : ℂ) + t * I)).re = 11 / 10 := by simp
  have hinv := Formalism.ZF.zetaInvBound_statement (((11 / 10 : ℝ) : ℂ) + t * I) (by rw [hz0re]; norm_num)
  have h1110 : (11 / 10 : ℝ) / (11 / 10 - 1) = 11 := by norm_num
  rw [hz0re, h1110] at hinv
  have hz0ne : riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; norm_num)
  have hpos : 0 < ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ := norm_pos_iff.mpr hz0ne
  have h11 : 1 ≤ ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ * 11 := by
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  have hT : 4 ≤ |t| + 2 := by linarith
  have hM1 : (1 : ℝ) ≤ 66 * (|t| + 2) := by linarith
  obtain ⟨Z, m, hZ, -, -, hbound⟩ := Formalism.ZF.landauLocal riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5)
    (66 * (|t| + 2)) (by norm_num) hM1
    (fun z hz => (differentiableAt_riemannZeta
      (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1).differentiableWithinAt)
    hz0ne
    (fun z hz => by
      have hb := (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.2
      nlinarith [mul_le_mul_of_nonneg_left h11 (by linarith : (0 : ℝ) ≤ 6 * (|t| + 2))])
  have hzmem : ((σ : ℂ) + t * I) ∈ Metric.closedBall (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5 / 6) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : (σ : ℂ) + t * I - (((11 / 10 : ℝ) : ℂ) + t * I) = ((σ - 11 / 10 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzre : ((σ : ℂ) + t * I).re = σ := by simp
  have hzne : riemannZeta ((σ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ)
  have hb := hbound _ hzmem hzne
  have hsum : 0 ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρ0 := ((hZ ρ).mp hρ).2
    have hρre : ρ.re ≤ 1 := by
      by_contra h
      push_neg at h
      exact riemannZeta_ne_zero_of_one_lt_re h hρ0
    apply re_natCast_div_nonneg
    simp
    linarith
  have hneg := neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
      ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))
  have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
      (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
        ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))).re -
        (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    simp only [Complex.neg_re, Complex.sub_re]; ring
  have hlogM : Real.log (66 * (|t| + 2)) ≤ 7 * Real.log (|t| + 2) := by
    have h6 : (4 : ℝ) ^ 6 ≤ (|t| + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) hT 6
    have hle : 66 * (|t| + 2) ≤ (|t| + 2) ^ 7 := by
      have e7 : (|t| + 2) ^ 7 = (|t| + 2) ^ 6 * (|t| + 2) := by ring
      rw [e7]; nlinarith
    calc Real.log (66 * (|t| + 2)) ≤ Real.log ((|t| + 2) ^ 7) := Real.log_le_log (by linarith) hle
      _ = 7 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num
  have h72 : 72 * Real.log (66 * (|t| + 2)) / (3 / 5) = 120 * Real.log (66 * (|t| + 2)) := by ring
  rw [hsplit]
  linarith
end Formalism.ZeroFreeDirichlet
