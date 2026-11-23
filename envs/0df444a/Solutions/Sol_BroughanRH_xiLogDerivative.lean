-- Prove2me | solution 1 for BroughanRH.xiLogDerivative
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:55:54.139465+00:00
-- url     : https://prove2.me/submissions/da407f1a-90f5-418c-9f60-cbeeb4721d2e
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


private abbrev UU : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)

private noncomputable def gg (p : UU) (w : ℂ) : ℂ := 1 + w ^ 2 / (-p.1.val ^ 2)

private lemma key_UU : ∀ w : ℂ, Multipliable (fun p : UU => gg p w) ∧
    FP w / FP 0 = ∏' p : UU, gg p w :=
  XiPairingPublished.concrete_upper_paired_product

private lemma UU_re (p : UU) : p.1.val.re = 0 := by
  have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
    intro h; have := p.2.isLt; omega
  exact zero_re_of_order hord

private lemma UU_nonempty : Nonempty UU := by
  by_contra hU
  rw [not_nonempty_iff] at hU
  have h0 := FP_zero_ne
  have hc : ∀ w, FP w = FP 0 := by
    intro w
    have := (key_UU w).2
    rw [tprod_empty] at this
    field_simp at this
    exact this
  have e1 : FP (-1/2) = 1/2 := by unfold FP; ring_nf
  have e2 : FP (3/2) = (Real.pi : ℂ) / 6 := by
    rw [FP_eq]; norm_num; exact xiM_two
  have := (hc (3/2)).trans (hc (-1/2)).symm
  rw [e1, e2] at this
  have h3 : (Real.pi : ℂ) = 3 := by linear_combination 6 * this
  have : Real.pi = 3 := by exact_mod_cast h3
  linarith [Real.pi_gt_three]

/-- Cross-multiplied comparison isolating one factor. -/
private lemma cross (p0 : UU) {wa wb : ℂ} (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖gg p0 wb‖ * ‖FP wa‖ ≤ ‖gg p0 wa‖ * ‖FP wb‖ := by
  have h0 := FP_zero_ne
  have hP : ∀ w, FP w = FP 0 * ∏' p : UU, gg p w := by
    intro w; rw [← (key_UU w).2]; field_simp
  have hgle : ∀ p : UU, ‖gg p wa‖ ≤ ‖gg p wb‖ := fun p =>
    (factor_lt (UU_re p) p.1.2 him hX).le
  have hTa := (key_UU wa).1.hasProd.norm
  have hTb := (key_UU wb).1.hasProd.norm
  have hlim : ‖gg p0 wb‖ * ‖∏' p : UU, gg p wa‖ ≤ ‖gg p0 wa‖ * ‖∏' p : UU, gg p wb‖ := by
    apply le_of_tendsto_of_tendsto (hTa.const_mul _) (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop {p0}] with S hS
    have hp0 : p0 ∈ S := Finset.singleton_subset_iff.mp hS
    rw [← Finset.mul_prod_erase S _ hp0, ← Finset.mul_prod_erase S (fun p => ‖gg p wb‖) hp0]
    have : ∏ x ∈ S.erase p0, ‖gg x wa‖ ≤ ∏ x ∈ S.erase p0, ‖gg x wb‖ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hgle i)
    have hn : 0 ≤ ‖gg p0 wb‖ * ‖gg p0 wa‖ := by positivity
    calc ‖gg p0 wb‖ * (‖gg p0 wa‖ * ∏ x ∈ S.erase p0, ‖gg x wa‖)
        = (‖gg p0 wb‖ * ‖gg p0 wa‖) * ∏ x ∈ S.erase p0, ‖gg x wa‖ := by ring
      _ ≤ (‖gg p0 wb‖ * ‖gg p0 wa‖) * ∏ x ∈ S.erase p0, ‖gg x wb‖ :=
          mul_le_mul_of_nonneg_left this hn
      _ = ‖gg p0 wa‖ * (‖gg p0 wb‖ * ∏ x ∈ S.erase p0, ‖gg x wb‖) := by ring
  rw [hP wa, hP wb, norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hlim (norm_nonneg (FP 0))
  linarith [this]

/-- Squared modulus of one factor. -/
private lemma gg_sq (p : UU) (w : ℂ) :
    ‖gg p w‖ ^ 2 * (p.1.val.im ^ 2) ^ 2 =
      (p.1.val.im ^ 2 + w.re ^ 2 - w.im ^ 2) ^ 2 + (2 * w.re * w.im) ^ 2 := by
  have hre := UU_re p
  have hpos := p.1.2
  set a := p.1.val
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : gg p w = (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    unfold gg; rw [ha]; field_simp
  rw [hrw, norm_div, div_pow, Complex.sq_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc, Complex.normSq_apply]
  field_simp
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

private lemma logderiv_pos {s : ℂ} (hs : 1/2 < s.re) :
    0 < (deriv xiM s / xiM s).re := by
  have hdiff : Differentiable ℂ xiM := by
    intro z; unfold xiM; have := differentiable_completedZeta₀; fun_prop
  have hxs : xiM s ≠ 0 := by
    intro h; have := xiM_zero_re h; linarith
  obtain ⟨p0⟩ := UU_nonempty
  set γ := p0.1.val.im with hγ
  have hγpos : 0 < γ := p0.1.2
  set w0 : ℂ := s - 1/2 with hw0
  have hx0 : 0 < w0.re := by simp [hw0]; linarith
  -- the function along the horizontal direction
  let φ : ℝ → ℂ := fun h => xiM (s + h)
  let N : ℝ → ℝ := fun h => ‖φ h‖ ^ 2
  have hφ : HasDerivAt φ (deriv xiM s) 0 := by
    have h0 : HasDerivAt xiM (deriv xiM s) (s + ((0:ℝ):ℂ)) := by
      simpa using (hdiff s).hasDerivAt
    exact (h0.comp_const_add s ((0:ℝ):ℂ)).comp_ofReal
  have hN := hφ.norm_sq
  set d := 2 * inner ℝ (φ 0) (deriv xiM s) with hd
  have hφ0 : φ 0 = xiM s := by simp [φ]
  have hFP : ∀ h : ℝ, φ h = FP (w0 + h) := by
    intro h; simp only [φ, FP_eq, hw0]; ring_nf
  -- lower bound on the slope
  have hA0 : 0 < ‖gg p0 w0‖ := by
    rcases (norm_nonneg (gg p0 w0)).eq_or_lt with h | h
    · exfalso
      have hc := cross p0 (wa := w0) (wb := w0 + 1) (by simp) (by simp; nlinarith)
      rw [← h, zero_mul] at hc
      have hlt := factor_lt (UU_re p0) p0.1.2 (wa := w0) (wb := w0 + 1) (by simp) (by simp; nlinarith)
      have : 0 < ‖FP w0‖ := by
        have e := hFP 0
        simp only [Complex.ofReal_zero, add_zero] at e
        rw [← e, hφ0]; exact norm_pos_iff.mpr hxs
      have hg1 : 0 < ‖gg p0 (w0 + 1)‖ := by
        unfold gg at h ⊢; linarith
      nlinarith [mul_pos hg1 this]
    · exact h
  set A0 := ‖gg p0 w0‖
  set κ : ℝ := N 0 * (4 * w0.re / γ ^ 2) / A0 ^ 2 with hκ
  have hN0 : 0 < N 0 := by
    show 0 < ‖φ 0‖ ^ 2
    rw [hφ0]; exact pow_pos (norm_pos_iff.mpr hxs) 2
  have hκpos : 0 < κ := by
    rw [hκ]; have : 0 < 4 * w0.re / γ ^ 2 := by positivity
    positivity
  have hslope : ∀ h : ℝ, 0 < h → κ ≤ slope N 0 h := by
    intro h hh
    rw [slope_def_field, sub_zero]
    have hc := cross p0 (wa := w0) (wb := w0 + h) (by simp) (by simp; nlinarith)
    have hsq := gg_sq p0 w0
    have hsq' := gg_sq p0 (w0 + h)
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      add_zero] at hsq'
    rw [← hγ] at hsq hsq'
    have hNh : N h = ‖FP (w0 + h)‖ ^ 2 := by simp [N, hFP]
    have hN0' : N 0 = ‖FP w0‖ ^ 2 := by simp [N, hFP]
    -- squared cross inequality
    have hc2 : ‖gg p0 (w0 + h)‖ ^ 2 * N 0 ≤ A0 ^ 2 * N h := by
      rw [hNh, hN0']
      have := mul_le_mul hc hc (by positivity) (by positivity)
      nlinarith [this]
    -- growth of the factor
    have hgrow : A0 ^ 2 + 4 * w0.re * h / γ ^ 2 ≤ ‖gg p0 (w0 + h)‖ ^ 2 := by
      have hγ4 : 0 < (γ ^ 2) ^ 2 := by positivity
      have key : (A0 ^ 2 + 4 * w0.re * h / γ ^ 2) * (γ ^ 2) ^ 2 ≤
          ‖gg p0 (w0 + h)‖ ^ 2 * (γ ^ 2) ^ 2 := by
        rw [hsq']
        have : (A0 ^ 2 + 4 * w0.re * h / γ ^ 2) * (γ ^ 2) ^ 2 =
            A0 ^ 2 * (γ ^ 2) ^ 2 + 4 * w0.re * h * γ ^ 2 := by
          field_simp
        rw [this, hsq]
        nlinarith [mul_pos hx0 hh, sq_nonneg w0.im, sq_nonneg w0.re, mul_pos (mul_pos hx0 hh) hγpos,
          mul_nonneg (mul_nonneg hx0.le hh.le) (sq_nonneg w0.im), sq_nonneg h,
          mul_nonneg (sq_nonneg h) (sq_nonneg w0.im), mul_nonneg hh.le (sq_nonneg w0.im),
          mul_nonneg (mul_nonneg hx0.le hh.le) (sq_nonneg w0.re),
          mul_nonneg (sq_nonneg h) (sq_nonneg w0.re), mul_nonneg hh.le hx0.le, pow_pos hh 3,
          pow_pos hh 4, mul_nonneg (mul_nonneg hh.le hh.le) (mul_nonneg hx0.le hx0.le)]
      exact le_of_mul_le_mul_right key hγ4
    have hA0sq : 0 < A0 ^ 2 := by positivity
    rw [hκ, div_le_div_iff₀ hA0sq hh]
    have hN0nn := hN0.le
    have := mul_le_mul_of_nonneg_right hgrow hN0nn
    rw [show 4 * w0.re * h / γ ^ 2 = (4 * w0.re / γ ^ 2) * h by ring] at this
    linarith [this, hc2]
  -- pass to the limit
  have hlim : Tendsto (slope N 0) (𝓝[>] 0) (𝓝 d) := by
    have := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0:ℝ)) (by simp)).mp
      hN.hasDerivWithinAt
    exact this
  have hdk : κ ≤ d := ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun h hh => hslope h hh)
  have hdpos : 0 < d := lt_of_lt_of_le hκpos hdk
  rw [hd, hφ0, Complex.inner] at hdpos
  -- Re (ξ'/ξ) = Re (ξ' * conj ξ) / |ξ|^2
  have hns : 0 < Complex.normSq (xiM s) := Complex.normSq_pos.mpr hxs
  rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_pos (by linarith) (inv_pos.mpr hns)

theorem solution :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ s : ℂ, 1/2 < s.re → 0 < (deriv xi s / xi s).re := by
  intro xi s hs
  exact logderiv_pos hs
