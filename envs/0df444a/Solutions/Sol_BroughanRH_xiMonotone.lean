-- Prove2me | solution 1 for BroughanRH.xiMonotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:51:04.062917+00:00
-- url     : https://prove2.me/submissions/80b62054-d41f-484b-aea6-b2e32cf904eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_XiHadamardPortPublished_concrete_xi_no_real_zeros

open Filter Topology

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
private lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

private noncomputable def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

/-- Under RH, zeros of `xiM` lie on the critical line. -/
private lemma xiM_zero_re {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply riemann_hypothesis s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

private noncomputable def FP (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

private lemma FP_eq (z : ℂ) : FP z = xiM (z + 1/2) := by
  unfold FP xiM; ring

private lemma FP_ne_zero {w : ℂ} (hw : w.re ≠ 0) : FP w ≠ 0 := by
  rw [FP_eq]
  intro h
  have := xiM_zero_re h
  simp at this
  exact hw this

private lemma FP_zero_ne : FP 0 ≠ 0 := by
  have := XiHadamardPortPublished.concrete_xi_no_real_zeros (1/2 : ℝ)
  rw [FP_eq, xiM]
  simpa using this

private lemma xiM_two : xiM 2 = (Real.pi : ℂ) / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Complex.Gammaℝ_def]
    norm_num [Complex.cpow_neg_one]
  have h2 : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
    have := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
    rw [riemannZeta_two, hG, div_inv_eq_mul] at this
    have h3 : completedRiemannZeta 2 * Real.pi = (Real.pi : ℂ) / 6 * Real.pi := by
      rw [← this]; ring
    exact mul_right_cancel₀ hpi h3
  have h0 := completedRiemannZeta_eq 2
  rw [h2] at h0
  unfold xiM
  have : completedRiemannZeta₀ 2 = (Real.pi : ℂ) / 6 + 1/2 + 1/(1-2) := by
    linear_combination -h0
  rw [this]; norm_num; ring

private lemma factor_lt {a wa wb : ℂ} (hre : a.re = 0) (hpos : 0 < a.im)
    (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖1 + wa ^ 2 / (-a ^ 2)‖ < ‖1 + wb ^ 2 / (-a ^ 2)‖ := by
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : ∀ w : ℂ, 1 + w ^ 2 / (-a ^ 2) = (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    intro w; rw [ha]; field_simp
  rw [hrw, hrw, norm_div, norm_div]
  apply div_lt_div_of_pos_right _ (by simpa using hc)
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im, zero_add]
  rw [him] at *
  have hX' : wa.re * wa.re < wb.re * wb.re := by nlinarith
  have hpos2 : 0 < 2 * (a.im * a.im) + 2 * (wb.im * wb.im) + wa.re * wa.re + wb.re * wb.re := by
    nlinarith [mul_self_nonneg wb.im, mul_self_nonneg wa.re, mul_self_nonneg wb.re]
  nlinarith [mul_pos (sub_pos.mpr hX') hpos2]

private lemma zero_re_of_order {a : ℂ} (h : analyticOrderNatAt FP a ≠ 0) : a.re = 0 := by
  have h1 : analyticOrderAt FP a ≠ 0 := by
    intro h0; apply h; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FP_eq] at h2
  have := xiM_zero_re h2
  simpa using this

private lemma main_lt {wa wb : ℂ} (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖FP wa‖ < ‖FP wb‖ := by
  let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)
  have key : ∀ w : ℂ, Multipliable (fun p : U => 1+w^2/(-p.1.val^2)) ∧
      FP w / FP 0 = ∏' p : U, (1+w^2/(-p.1.val^2)) :=
    XiPairingPublished.concrete_upper_paired_product
  have h0 := FP_zero_ne
  have hwb : wb.re ≠ 0 := by
    intro h; rw [h] at hX; nlinarith [sq_nonneg wa.re]
  have hFb := FP_ne_zero hwb
  have hP : ∀ w, FP w = FP 0 * ∏' p : U, (1+w^2/(-p.1.val^2)) := by
    intro w; rw [← (key w).2]; field_simp
  -- nonempty
  have hne : Nonempty U := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    have hc : ∀ w, FP w = FP 0 := by intro w; rw [hP w, tprod_empty, mul_one]
    have e1 : FP (-1/2) = 1/2 := by unfold FP; ring_nf
    have e2 : FP (3/2) = (Real.pi : ℂ) / 6 := by
      rw [FP_eq]; norm_num; exact xiM_two
    have := (hc (3/2)).trans (hc (-1/2)).symm
    rw [e1, e2] at this
    have h3 : (Real.pi : ℂ) = 3 := by linear_combination 6 * this
    have : Real.pi = 3 := by exact_mod_cast h3
    linarith [Real.pi_gt_three]
  obtain ⟨p0⟩ := hne
  set g : U → ℂ → ℂ := fun p w => 1+w^2/(-p.1.val^2) with hg
  have hgle : ∀ p : U, ‖g p wa‖ < ‖g p wb‖ := by
    intro p
    have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
      intro h; have := p.2.isLt; omega
    exact factor_lt (zero_re_of_order hord) p.1.2 him hX
  set Pa := ‖∏' p : U, g p wa‖
  set Pb := ‖∏' p : U, g p wb‖
  have hTa := (key wa).1.hasProd.norm
  have hTb := (key wb).1.hasProd.norm
  have hlim : ‖g p0 wb‖ * Pa ≤ ‖g p0 wa‖ * Pb := by
    apply le_of_tendsto_of_tendsto (hTa.const_mul _) (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop {p0}] with S hS
    have hp0 : p0 ∈ S := Finset.singleton_subset_iff.mp hS
    rw [← Finset.mul_prod_erase S _ hp0, ← Finset.mul_prod_erase S (fun p => ‖g p wb‖) hp0]
    have : ∏ x ∈ S.erase p0, ‖g x wa‖ ≤ ∏ x ∈ S.erase p0, ‖g x wb‖ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (hgle i).le)
    have hn : 0 ≤ ‖g p0 wb‖ * ‖g p0 wa‖ := by positivity
    calc ‖g p0 wb‖ * (‖g p0 wa‖ * ∏ x ∈ S.erase p0, ‖g x wa‖)
        = (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wa‖ := by ring
      _ ≤ (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wb‖ :=
          mul_le_mul_of_nonneg_left this hn
      _ = ‖g p0 wa‖ * (‖g p0 wb‖ * ∏ x ∈ S.erase p0, ‖g x wb‖) := by ring
  have hna : ‖FP wa‖ = ‖FP 0‖ * Pa := by rw [hP wa, norm_mul]
  have hnb : ‖FP wb‖ = ‖FP 0‖ * Pb := by rw [hP wb, norm_mul]
  have hF0 : 0 < ‖FP 0‖ := norm_pos_iff.mpr h0
  rw [hna, hnb]
  apply mul_lt_mul_of_pos_left _ hF0
  have hPb : 0 < Pb := by
    have : 0 < ‖FP wb‖ := norm_pos_iff.mpr hFb
    rw [hnb] at this
    exact pos_of_mul_pos_right this hF0.le
  rcases (norm_nonneg (∏' p : U, g p wa)).eq_or_lt with hPa | hPa
  · change 0 = Pa at hPa
    rw [← hPa]; exact hPb
  change 0 < Pa at hPa
  have hA := norm_nonneg (g p0 wa)
  have hAB := hgle p0
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon hA, mul_lt_mul_of_pos_right hAB hPa]

private lemma xi_eq_FP (σ t : ℝ) :
    (1 + ((σ : ℂ) + (t : ℂ) * Complex.I) * (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ : ℂ) + (t : ℂ) * Complex.I)) / 2 =
      FP (((σ - 1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  rw [FP_eq, xiM]; push_cast; ring_nf

private lemma xi_lt_of_sq {σ₁ σ₂ t : ℝ} (h : (σ₁ - 1/2) ^ 2 < (σ₂ - 1/2) ^ 2) :
    ‖(1 + ((σ₁ : ℂ) + (t : ℂ) * Complex.I) * (((σ₁ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) / 2‖ <
    ‖(1 + ((σ₂ : ℂ) + (t : ℂ) * Complex.I) * (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) / 2‖ := by
  rw [xi_eq_FP, xi_eq_FP]
  apply main_lt
  · simp
  · simpa using h

theorem solution :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖xi (↑σ + ↑t * Complex.I)‖) (Set.Ioi (1/2 : ℝ)) := by
  intro xi t a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  exact xi_lt_of_sq (by nlinarith)
