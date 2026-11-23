-- Prove2me | solution 1 for BroughanRH.freitas
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:49:39.428337+00:00
-- url     : https://prove2.me/submissions/f987b3c6-409c-48f6-ad10-a84b3e6580de
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product

open Filter Topology Complex


lemma li_iter {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {W : Set ℂ}
    (hW : IsOpen W) (hF : ∀ i, DifferentiableOn ℂ (F i) W)
    (h : TendstoLocallyUniformlyOn F f φ W) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (F i)) (iteratedDeriv k f) φ W ∧
    ∀ i, DifferentiableOn ℂ (iteratedDeriv k (F i)) W := by
  induction k with
  | zero => simpa using ⟨h, hF⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, fun i => ?_⟩
    · simp only [iteratedDeriv_succ]
      exact h1.deriv (Eventually.of_forall h2) hW
    · rw [iteratedDeriv_succ]; exact (h2 i).deriv hW

lemma li_alg (n : ℕ) (τ c : ℂ) (hτ : τ ≠ 0) (hc : c - τ ≠ 0) :
    ∑ i ∈ Finset.range (n+1), ((n+1).choose i : ℂ) * τ^(n-i) * ((-1)^(n-i) / (τ - c)^(n+1-i))
      = (1 - (c/(c-τ))^(n+1)) / τ := by
  have hτc : τ - c ≠ 0 := by intro h; apply hc; linear_combination -h
  have key : ∀ i ∈ Finset.range (n+1), ((n+1).choose i : ℂ) * τ^(n-i) * ((-1)^(n-i) / (τ - c)^(n+1-i))
      = -(1/τ) * ((τ/(c-τ))^(n+1-i) * ((n+1).choose i : ℂ)) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, rfl⟩ : ∃ j, n = i + j := ⟨n - i, by omega⟩
    have e1 : i + j - i = j := by omega
    have e2 : i + j + 1 - i = j + 1 := by omega
    rw [e1, e2]
    obtain ⟨d, rfl⟩ : ∃ d, c = τ + d := ⟨c - τ, by ring⟩
    have hd : d ≠ 0 := by simpa using hc
    rw [show τ - (τ + d) = -d by ring, show τ + d - τ = d by ring, div_pow]
    have hm' : ((-1:ℂ)^j) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hx : ((-1:ℂ)^j) / (-d)^(j+1) = -(1/d^(j+1)) := by
      rw [neg_pow d, pow_succ (-1:ℂ)]; field_simp
    rw [hx]
    field_simp
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have hadd := add_pow (1 : ℂ) (τ/(c-τ)) (n+1)
  rw [Finset.sum_range_succ] at hadd
  simp only [one_pow, one_mul, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one] at hadd
  have hsum : ∑ x ∈ Finset.range (n + 1), (τ / (c - τ)) ^ (n + 1 - x) * ((n + 1).choose x : ℂ)
      = (1 + τ / (c - τ)) ^ (n + 1) - 1 := by rw [hadd]; ring
  rw [hsum]
  have : 1 + τ / (c - τ) = c / (c - τ) := by field_simp; ring
  rw [this]
  field_simp
  ring

lemma li_iter_inv (k : ℕ) (c x : ℂ) :
    iteratedDeriv k (fun w => (w - c)⁻¹) x = (-1)^k * k.factorial / (x - c)^(k+1) := by
  have := iteratedDeriv_comp_sub_const k (Inv.inv : ℂ → ℂ) c
  rw [show (fun w => (w - c)⁻¹) = (fun z => Inv.inv (z - c)) from rfl, this]
  simp only [iteratedDeriv_eq_iterate]
  rw [iter_deriv_inv]
  rw [show (-1 - (k:ℤ)) = -((k+1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    div_eq_mul_inv]

lemma li_log_bound (z : ℂ) (hz : 0 ≤ z.re) : ‖log (1 + z)‖ ≤ 10 * ‖z‖ := by
  rcases le_or_gt ‖z‖ (1/2) with h | h
  · have := norm_log_one_add_half_le_self h
    linarith [norm_nonneg z]
  · have h1 : 1 ≤ ‖1 + z‖ := by
      have : (1 + z).re ≤ ‖1 + z‖ := Complex.re_le_norm _
      simp at this; linarith
    have hre : (log (1+z)).re = Real.log ‖1+z‖ := Complex.log_re _
    have hre' : 0 ≤ Real.log ‖1+z‖ := Real.log_nonneg h1
    have hle : Real.log ‖1+z‖ ≤ ‖z‖ := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < ‖1+z‖)
      have := norm_add_le (1:ℂ) z
      simp at this
      linarith
    have him : |(log (1+z)).im| ≤ Real.pi := by
      rw [Complex.log_im]; exact Complex.abs_arg_le_pi _
    calc ‖log (1 + z)‖ ≤ |(log (1+z)).re| + |(log (1+z)).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ‖z‖ + Real.pi := by rw [hre, abs_of_nonneg hre']; linarith
      _ ≤ 10 * ‖z‖ := by nlinarith [Real.pi_lt_four]

/-- Derivatives of one paired logarithmic factor. -/
lemma li_term_deriv (a w0 : ℂ) (W : Set ℂ) (hW : IsOpen W) (hw0 : w0 ∈ W)
    (hslit : ∀ w ∈ W, 1 + w^2/(-a^2) ∈ slitPlane) (ha : a ≠ 0) (hwa : w0 - a ≠ 0)
    (hwa' : w0 + a ≠ 0) (k : ℕ) :
    iteratedDeriv (k+1) (fun w => log (1 + w^2/(-a^2))) w0
      = (-1)^k * k.factorial / (w0 - a)^(k+1) + (-1)^k * k.factorial / (w0 + a)^(k+1) := by
  rw [iteratedDeriv_succ']
  have hev : deriv (fun w => log (1 + w^2/(-a^2))) =ᶠ[𝓝 w0]
      (fun w => (w - a)⁻¹ + (w - (-a))⁻¹) := by
    have hU : IsOpen (W ∩ {w | w - a ≠ 0} ∩ {w | w + a ≠ 0}) := by
      refine (hW.inter ?_).inter ?_
      · exact isOpen_ne_fun (by fun_prop) (by fun_prop)
      · exact isOpen_ne_fun (by fun_prop) (by fun_prop)
    filter_upwards [hU.mem_nhds ⟨⟨hw0, hwa⟩, hwa'⟩] with w hw
    obtain ⟨⟨hwW, h1⟩, h2⟩ := hw
    have hs := hslit w hwW
    have hd : HasDerivAt (fun w => 1 + w^2/(-a^2)) (2 * w / (-a^2)) w := by
      exact (((hasDerivAt_pow 2 w).div_const (-a^2)).const_add 1).congr_deriv (by push_cast; ring)
    rw [(hd.clog hs).deriv]
    have ha2 : -a^2 ≠ 0 := by simpa using ha
    simp only [sub_neg_eq_add]
    have h1' : w - a ≠ 0 := h1
    have h2' : w + a ≠ 0 := h2
    have e : 1 + w^2/(-a^2) = (w-a)*(w+a)/(-a^2) := by field_simp; ring
    rw [e]
    field_simp
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev]
  rw [iteratedDeriv_fun_add]
  · rw [li_iter_inv, li_iter_inv, sub_neg_eq_add]
  · exact ((contDiffAt_id.sub contDiffAt_const).inv hwa)
  · exact ((contDiffAt_id.sub contDiffAt_const).inv (by simpa using hwa'))


noncomputable def xiL (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

noncomputable def FL (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

lemma FL_eq (z : ℂ) : FL z = xiL (z + 1/2) := by unfold FL xiL; ring

lemma xiL_differentiable : Differentiable ℂ xiL := by
  intro z; unfold xiL; have := differentiable_completedZeta₀; fun_prop

abbrev UL : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FL z.val)

lemma key_UL : ∀ w : ℂ, Multipliable (fun p : UL => 1 + w^2/(-p.1.val^2)) ∧
    FL w / FL 0 = ∏' p : UL, (1 + w^2/(-p.1.val^2)) :=
  XiPairingPublished.concrete_upper_paired_product

lemma li_completed_ne_zero {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

lemma xiL_zero_re {s : ℂ} (hx' : xiL s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiL at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (li_completed_ne_zero h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (li_completed_ne_zero this ?_)
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

lemma UL_re (p : UL) : p.1.val.re = 0 := by
  have hord : analyticOrderNatAt FL p.1.val ≠ 0 := by
    intro h; have := p.2.isLt; omega
  have h1 : analyticOrderAt FL p.1.val ≠ 0 := by
    intro h0; apply hord; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FL_eq] at h2
  have := xiL_zero_re h2
  simpa using this

lemma UL_sq (p : UL) : -p.1.val^2 = (((p.1.val.im)^2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [pow_two, UL_re p]

lemma li_prod_ge {α : Type*} (S : Finset α) (x : α → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 + ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 + x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 : 0 ≤ ∑ i ∈ S, x i := Finset.sum_nonneg (fun i _ => hx i)
    nlinarith [hx a]

lemma li_prod_real (x : ℝ) :
    (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).im = 0 ∧
    ∀ S : Finset UL, 1 + ∑ p ∈ S, x^2/(p.1.val.im)^2 ≤ (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).re := by
  set P := ∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))
  have hT := (key_UL x).1.hasProd
  have hfac : ∀ p : UL, (1 + (x:ℂ)^2/(-p.1.val^2)) = ((1 + x^2/(p.1.val.im)^2 : ℝ) : ℂ) := by
    intro p; rw [UL_sq]; push_cast; ring
  have hT' : Tendsto (fun S : Finset UL => (((∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) : ℝ)) : ℂ))
      atTop (𝓝 P) := by
    have := hT
    simp only [HasProd] at this
    refine this.congr (fun S => ?_)
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl (fun p _ => hfac p)
  constructor
  · have h := (Complex.continuous_im.tendsto P).comp hT'
    have : (fun S : Finset UL => (((∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) : ℝ)) : ℂ).im) = fun _ => 0 := by
      funext S; exact Complex.ofReal_im _
    simp only [Function.comp_def] at h
    rw [this] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)
  · intro S0
    have h := (Complex.continuous_re.tendsto P).comp hT'
    simp only [Function.comp_def, Complex.ofReal_re] at h
    have hnn : ∀ p : UL, 0 ≤ x^2/(p.1.val.im)^2 := fun p => by positivity
    refine ge_of_tendsto h ?_
    filter_upwards [Filter.eventually_ge_atTop S0] with S hS
    calc 1 + ∑ p ∈ S0, x^2/(p.1.val.im)^2 ≤ ∏ p ∈ S0, (1 + x^2/(p.1.val.im)^2) :=
          li_prod_ge S0 _ hnn
      _ ≤ ∏ p ∈ S, (1 + x^2/(p.1.val.im)^2) := by
          rw [← Finset.prod_sdiff hS]
          have h1 : 1 ≤ ∏ p ∈ S \ S0, (1 + x^2/(p.1.val.im)^2) := by
            have := li_prod_ge (S \ S0) _ hnn
            have : 0 ≤ ∑ p ∈ S \ S0, x^2/(p.1.val.im)^2 := Finset.sum_nonneg (fun i _ => hnn i)
            linarith
          have h2 : 0 ≤ ∏ p ∈ S0, (1 + x^2/(p.1.val.im)^2) :=
            Finset.prod_nonneg (fun p _ => by linarith [hnn p])
          nlinarith

lemma li_summable : Summable (fun p : UL => 1/(p.1.val.im)^2) := by
  have h := (li_prod_real 1).2
  refine summable_of_sum_le (c := Complex.re (∏' p : UL, (1 + ((1:ℝ):ℂ)^2/(-p.1.val^2))) - 1)
    (fun p => by positivity) (fun S => ?_)
  have := h S
  simp only [one_pow] at this
  linarith

lemma li_P_real (x : ℝ) : ∃ r : ℝ, 1 ≤ r ∧ (∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))) = (r:ℂ) := by
  obtain ⟨h1, h2⟩ := li_prod_real x
  refine ⟨(∏' p : UL, (1 + (x:ℂ)^2/(-p.1.val^2))).re, ?_, ?_⟩
  · simpa using h2 ∅
  · exact Complex.ext (by simp) (by simp [h1])

/-- The region. -/
def WL (R : ℝ) : Set ℂ := {w : ℂ | |w.im| < w.re} ∩ Metric.ball 0 R

lemma WL_open (R : ℝ) : IsOpen (WL R) :=
  (isOpen_lt (by fun_prop) (by fun_prop)).inter Metric.isOpen_ball

lemma WL_re (R : ℝ) (p : UL) (w : ℂ) (hw : w ∈ WL R) : 0 < (w^2/(-p.1.val^2)).re := by
  rw [UL_sq, Complex.div_ofReal_re]
  have hγ : 0 < p.1.val.im := p.1.2
  have : 0 < (w^2).re := by
    rw [pow_two, Complex.mul_re]
    have h : |w.im| < w.re := hw.1
    have h0 := abs_nonneg w.im
    have h3 : |w.im| * |w.im| < w.re * w.re := mul_self_lt_mul_self h0 h
    rw [abs_mul_abs_self] at h3
    linarith
  positivity

lemma WL_slit (R : ℝ) (p : UL) (w : ℂ) (hw : w ∈ WL R) : 1 + w^2/(-p.1.val^2) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have := WL_re R p w hw
  simp; linarith

noncomputable def phiL (p : UL) (w : ℂ) : ℂ := log (1 + w^2/(-p.1.val^2))

lemma phiL_bound (R : ℝ) (p : UL) (w : ℂ) (hw : w ∈ WL R) :
    ‖phiL p w‖ ≤ (10 * R^2) * (1/(p.1.val.im)^2) := by
  have h := li_log_bound _ (WL_re R p w hw).le
  unfold phiL
  refine h.trans ?_
  rw [UL_sq, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hγ : 0 < p.1.val.im := p.1.2
  have hR : ‖w‖ < R := by simpa using hw.2
  rw [abs_of_pos (by positivity)]
  have : ‖w‖^2 ≤ R^2 := by nlinarith [norm_nonneg w]
  have h3 : ‖w‖ ^ 2 / p.1.val.im ^ 2 ≤ R^2 / p.1.val.im ^ 2 := by gcongr
  calc 10 * (‖w‖ ^ 2 / p.1.val.im ^ 2) ≤ 10 * (R^2 / p.1.val.im ^ 2) := by linarith
    _ = _ := by ring

lemma phiL_diff (R : ℝ) (p : UL) : DifferentiableOn ℂ (phiL p) (WL R) := by
  intro w hw
  apply DifferentiableAt.differentiableWithinAt
  unfold phiL
  exact (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 + w^2/(-p.1.val^2)) w).clog
    (WL_slit R p w hw)

noncomputable def LL (w : ℂ) : ℂ := ∑' p : UL, phiL p w

lemma LL_unif (R : ℝ) : TendstoUniformlyOn (fun S : Finset UL => fun w => ∑ p ∈ S, phiL p w)
    LL atTop (WL R) :=
  tendstoUniformlyOn_tsum (li_summable.mul_left (10 * R^2)) (fun p w hw => phiL_bound R p w hw)

lemma LL_diff (R : ℝ) : DifferentiableOn ℂ LL (WL R) :=
  (LL_unif R).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun S => DifferentiableOn.fun_sum fun p _ => phiL_diff R p) (WL_open R)

lemma LL_exp (R : ℝ) (w : ℂ) (hw : w ∈ WL R) : exp (LL w) = FL w / FL 0 := by
  have h1 : Tendsto (fun S : Finset UL => exp (∑ p ∈ S, phiL p w)) atTop (𝓝 (exp (LL w))) :=
    (Complex.continuous_exp.tendsto _).comp ((LL_unif R).tendsto_at hw)
  have h2 := (key_UL w).1.hasProd
  rw [(key_UL w).2]
  refine tendsto_nhds_unique h1 (h2.congr (fun S => ?_))
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  unfold phiL
  rw [Complex.exp_log (slitPlane_ne_zero (WL_slit R p w hw))]


lemma FL_zero_ne : FL 0 ≠ 0 := by
  intro h
  have k := (key_UL ((1/2 : ℝ) : ℂ)).2
  rw [h, div_zero] at k
  obtain ⟨r, hr, hr'⟩ := li_P_real (1/2)
  rw [hr'] at k
  have : r = 0 := by exact_mod_cast k.symm
  linarith

lemma FL_pos (x : ℝ) : ∃ r : ℝ, 0 < r ∧ FL x = r := by
  obtain ⟨r1, h1, e1⟩ := li_P_real x
  obtain ⟨r2, h2, e2⟩ := li_P_real (1/2)
  have k1 := (key_UL x).2
  have k2 := (key_UL ((1/2:ℝ):ℂ)).2
  rw [e1] at k1; rw [e2] at k2
  have hhalf : FL ((1/2:ℝ):ℂ) = 1/2 := by unfold FL; push_cast; ring_nf
  have h0 := FL_zero_ne
  rw [hhalf, div_eq_iff h0] at k2
  rw [div_eq_iff h0] at k1
  refine ⟨r1/(2*r2), by positivity, ?_⟩
  have hr2 : (r2:ℂ) ≠ 0 := by exact_mod_cast (by linarith : r2 ≠ 0)
  rw [k1]; push_cast
  field_simp
  linear_combination (-2 * (r1:ℂ)) * k2

lemma li_local (τ : ℝ) (hτ : 1 ≤ τ) :
    (fun s => log (xiL s)) =ᶠ[𝓝 (τ:ℂ)]
      (fun s => (log (xiL τ) - LL ((τ:ℂ) - 1/2)) + LL (s - 1/2)) := by
  set R := τ + 1 with hR
  set w0 : ℂ := (τ:ℂ) - 1/2 with hw0def
  have hw0r : w0 = ((τ - 1/2 : ℝ) : ℂ) := by rw [hw0def]; push_cast; ring
  have hw0 : w0 ∈ WL R := by
    rw [hw0r]
    refine ⟨?_, ?_⟩
    · show |((τ - 1/2 : ℝ) : ℂ).im| < ((τ - 1/2 : ℝ) : ℂ).re
      simp; linarith
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
  obtain ⟨r, hr, hxr⟩ := FL_pos (τ - 1/2)
  have hxi : xiL τ = r := by rw [← hxr, FL_eq]; push_cast; ring_nf
  have hslit : xiL τ ∈ slitPlane := by rw [hxi]; exact ofReal_mem_slitPlane.2 hr
  have hc1 : ContinuousAt (fun s => log (xiL s)) τ :=
    (xiL_differentiable.continuous.continuousAt).clog hslit
  have hLc : ContinuousAt LL w0 :=
    (LL_diff R).continuousOn.continuousAt ((WL_open R).mem_nhds hw0)
  have hc2 : ContinuousAt (fun s : ℂ => LL (s - 1/2)) τ :=
    ContinuousAt.comp (g := LL) (f := fun s : ℂ => s - 1/2) hLc (by fun_prop)
  set h : ℂ → ℂ := fun s => log (xiL s) - ((log (xiL τ) - LL w0) + LL (s - 1/2)) with hdef
  have hcont : ContinuousAt h τ := hc1.sub (continuousAt_const.add hc2)
  have h0 : h τ = 0 := by simp only [hdef, hw0def]; ring
  have hev1 : ∀ᶠ s in 𝓝 (τ:ℂ), ‖h s‖ < 1 := by
    have := hcont.eventually (Metric.ball_mem_nhds (h τ) one_pos)
    filter_upwards [this] with s hs
    rw [h0, dist_zero_right] at hs; exact hs
  have hev2 : ∀ᶠ s in 𝓝 (τ:ℂ), s - 1/2 ∈ WL R :=
    (by fun_prop : Continuous fun s : ℂ => s - 1/2).continuousAt.preimage_mem_nhds
      ((WL_open R).mem_nhds hw0)
  have hev3 : ∀ᶠ s in 𝓝 (τ:ℂ), xiL s ≠ 0 :=
    xiL_differentiable.continuous.continuousAt.eventually_ne (slitPlane_ne_zero hslit)
  filter_upwards [hev1, hev2, hev3] with s h1 h2 h3
  have hFw0 : FL w0 = xiL τ := by rw [FL_eq, hw0def]; ring_nf
  have hFs : FL (s - 1/2) = xiL s := by rw [FL_eq]; ring_nf
  have hexp : exp (log (xiL s)) = exp ((log (xiL τ) - LL w0) + LL (s - 1/2)) := by
    rw [exp_log h3, exp_add, exp_sub, exp_log (slitPlane_ne_zero hslit), LL_exp R _ h2,
      LL_exp R _ hw0, hFw0, hFs]
    have := FL_zero_ne
    have := slitPlane_ne_zero hslit
    field_simp
  obtain ⟨m, hm⟩ := exp_eq_exp_iff_exists_int.mp hexp
  have hhs : h s = m * (2 * Real.pi * I) := by simp only [hdef]; rw [hm]; ring
  show log (xiL s) = (log (xiL τ) - LL w0) + LL (s - 1/2)
  rcases eq_or_ne m 0 with hm0 | hm0
  · rw [hm, hm0]; simp
  · exfalso
    rw [hhs] at h1
    have : ‖(m:ℂ) * (2 * Real.pi * I)‖ = |(m:ℝ)| * (2 * Real.pi) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_intCast]
      simp [abs_of_pos Real.pi_pos]
    rw [this] at h1
    have hm1 : (1:ℝ) ≤ |(m:ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
    nlinarith [Real.pi_gt_three]

lemma li_comb (n : ℕ) (τ a : ℂ) (hτ : τ ≠ 0) (h1 : 1/2 + a - τ ≠ 0) (h2 : 1/2 - a - τ ≠ 0) :
    ∑ i ∈ Finset.range (n+1), ((n+1).choose i : ℂ) * ((n.descFactorial i : ℂ) * τ^(n-i)) *
      ((-1)^(n-i) * ((n-i).factorial : ℂ) / (τ - 1/2 - a)^(n-i+1) +
        (-1)^(n-i) * ((n-i).factorial : ℂ) / (τ - 1/2 + a)^(n-i+1))
      = (n.factorial : ℂ) * ((1 - ((1/2+a)/((1/2+a)-τ))^(n+1))/τ +
          (1 - ((1/2-a)/((1/2-a)-τ))^(n+1))/τ) := by
  rw [← li_alg n τ (1/2+a) hτ h1, ← li_alg n τ (1/2-a) hτ h2, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hf : ((n-i).factorial : ℂ) * (n.descFactorial i : ℂ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hi'
  have e : n + 1 - i = n - i + 1 := by omega
  rw [e, ← hf]
  have e1 : τ - (1/2 + a) = τ - 1/2 - a := by ring
  have e2 : τ - (1/2 - a) = τ - 1/2 + a := by ring
  rw [e1, e2]
  ring

theorem li_formula (τ : ℝ) (hτ : 1 ≤ τ) (n : ℕ) :
    Tendsto (fun S : Finset UL => ∑ p ∈ S, (n.factorial : ℂ) *
      ((1 - ((1/2 + p.1.val)/((1/2 + p.1.val) - τ))^(n+1))/τ +
        (1 - ((1/2 - p.1.val)/((1/2 - p.1.val) - τ))^(n+1))/τ))
      atTop (𝓝 (iteratedDeriv (n+1) (fun s : ℂ => s^n * log (xiL s)) τ)) := by
  set R := τ + 1 with hR
  set w0 : ℂ := (τ:ℂ) - 1/2 with hw0def
  have hw0r : w0 = ((τ - 1/2 : ℝ) : ℂ) := by rw [hw0def]; push_cast; ring
  have hw0 : w0 ∈ WL R := by
    rw [hw0r]
    refine ⟨?_, ?_⟩
    · show |((τ - 1/2 : ℝ) : ℂ).im| < ((τ - 1/2 : ℝ) : ℂ).re
      simp; linarith
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
  obtain ⟨r, hr, hxr⟩ := FL_pos (τ - 1/2)
  have hxi : xiL τ = r := by rw [← hxr, FL_eq]; push_cast; ring_nf
  have hslit : xiL τ ∈ slitPlane := by rw [hxi]; exact ofReal_mem_slitPlane.2 hr
  have hD : ∀ m : ℕ, Tendsto (fun S : Finset UL => ∑ p ∈ S, iteratedDeriv (m+1) (phiL p) w0)
      atTop (𝓝 (iteratedDeriv (m+1) (fun s => log (xiL s)) τ)) := by
    intro m
    rw [Filter.EventuallyEq.iteratedDeriv_eq (m+1) (li_local τ hτ),
      iteratedDeriv_const_add (Nat.succ_pos m), iteratedDeriv_comp_sub_const]
    have hl := ((li_iter (WL_open R) (fun S => DifferentiableOn.fun_sum fun p _ => phiL_diff R p)
      (LL_unif R).tendstoLocallyUniformlyOn (m+1)).1.tendsto_at hw0)
    refine hl.congr (fun S => ?_)
    exact iteratedDeriv_fun_sum (fun p _ =>
      ((phiL_diff R p).analyticAt ((WL_open R).mem_nhds hw0)).contDiffAt)
  have han : AnalyticAt ℂ (fun s => log (xiL s)) τ :=
    (xiL_differentiable.analyticAt _).clog hslit
  rw [iteratedDeriv_fun_mul (by fun_prop) han.contDiffAt, Finset.sum_range_succ]
  simp only [iteratedDeriv_pow]
  rw [Nat.descFactorial_of_lt (by omega)]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  have hlim := tendsto_finsetSum (Finset.range (n+1)) (fun i _ =>
    (hD (n - i)).const_mul (((n+1).choose i : ℂ) * ((n.descFactorial i : ℂ) * (τ:ℂ)^(n-i))))
  have e : ∀ i ∈ Finset.range (n+1), ((n+1).choose i : ℂ) * ((n.descFactorial i : ℂ) * (τ:ℂ)^(n-i)) *
      iteratedDeriv (n + 1 - i) (fun s => log (xiL s)) τ =
      ((n+1).choose i : ℂ) * ((n.descFactorial i : ℂ) * (τ:ℂ)^(n-i)) *
      iteratedDeriv (n - i + 1) (fun s => log (xiL s)) τ := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show n + 1 - i = n - i + 1 by omega]
  rw [Finset.sum_congr rfl e]
  refine hlim.congr (fun S => ?_)
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre := UL_re p
  have him : 0 < p.1.val.im := p.1.2
  have ha : p.1.val ≠ 0 := by intro h; rw [h] at him; simp at him
  have hw0re : w0.re = τ - 1/2 := by rw [hw0r]; simp
  have hne1 : w0 - p.1.val ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre, hw0re] at this; linarith
  have hne2 : w0 + p.1.val ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre, hw0re] at this; linarith
  have hτ0 : (τ:ℂ) ≠ 0 := by exact_mod_cast (by linarith : τ ≠ 0)
  have h1 : 1/2 + p.1.val - τ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this; linarith
  have h2 : 1/2 - p.1.val - τ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hre] at this; linarith
  rw [← li_comb n τ p.1.val hτ0 h1 h2]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold phiL
  rw [li_term_deriv p.1.val w0 (WL R) (WL_open R) hw0 (fun w hw => WL_slit R p w hw) ha hne1 hne2]
lemma li_norm_le (c : ℂ) (hc : c.re = 1/2) (τ : ℝ) (hτ : 1 ≤ τ) : ‖c/(c-τ)‖ ≤ 1 := by
  have hne : c - τ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [hc] at this; linarith
  rw [norm_div, div_le_one (norm_pos_iff.2 hne)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp [hc]; nlinarith

lemma li_re_nonneg (c : ℂ) (hc : c.re = 1/2) (τ : ℝ) (hτ : 1 ≤ τ) (N : ℕ) :
    0 ≤ ((1 - (c/(c-τ))^N)/τ).re := by
  rw [Complex.div_ofReal_re]
  apply div_nonneg _ (by linarith)
  have := li_norm_le c hc τ hτ
  have h1 : ‖(c/(c-τ))^N‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) this
  have h2 := Complex.re_le_norm ((c/(c-τ))^N)
  simp only [sub_re, one_re]; linarith

lemma li_term_nonneg (τ : ℝ) (hτ : 1 ≤ τ) (n : ℕ) (p : UL) :
    0 ≤ ((1 - ((1/2 + p.1.val)/((1/2 + p.1.val) - τ))^(n+1))/τ +
        (1 - ((1/2 - p.1.val)/((1/2 - p.1.val) - τ))^(n+1))/τ).re := by
  have hre := UL_re p
  rw [add_re]
  exact add_nonneg (li_re_nonneg _ (by simp [hre]) τ hτ _) (li_re_nonneg _ (by simp [hre]) τ hτ _)

lemma li_re_formula (τ : ℝ) (hτ : 1 ≤ τ) (n : ℕ) :
    Tendsto (fun S : Finset UL => ∑ p ∈ S,
      ((1 - ((1/2 + p.1.val)/((1/2 + p.1.val) - τ))^(n+1))/τ +
        (1 - ((1/2 - p.1.val)/((1/2 - p.1.val) - τ))^(n+1))/τ).re)
      atTop (𝓝 (((iteratedDeriv (n+1) (fun s : ℂ => s^n * log (xiL s)) τ) / (n.factorial : ℂ)).re)) := by
  have h := ((li_formula τ hτ n).div_const (n.factorial : ℂ))
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have h2 := (Complex.continuous_re.tendsto _).comp h
  refine h2.congr (fun S => ?_)
  simp only [Function.comp_def, ← Finset.sum_div, ← Finset.mul_sum]
  rw [mul_div_cancel_left₀ _ hf, Complex.re_sum]

theorem li_freitas (τ : ℝ) (hτ : 1 ≤ τ) (n : ℕ) :
    0 ≤ (((iteratedDeriv (n+1) (fun s : ℂ => s^n * log (xiL s)) τ) / (n.factorial : ℂ)).re) :=
  ge_of_tendsto' (li_re_formula τ hτ n) (fun S => Finset.sum_nonneg (fun p _ => li_term_nonneg τ hτ n p))


theorem solution :
    let xi (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2
    ∀ τ : ℝ, 1 ≤ τ → ∀ n : ℕ, 0 ≤ ((iteratedDeriv (n+1) (fun s : ℂ => s^n * Complex.log (xi s)) (τ : ℂ)) / (n.factorial : ℂ)).re := by
  intro xi τ hτ n
  exact li_freitas τ hτ n

