-- Prove2me | solution 1 for CVPricing.Regret.optPrice_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T21:31:20.484269+00:00
-- url     : https://prove2.me/submissions/8eeb311c-2ff1-41bb-8c6b-55d00cfa65d5

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

set_option autoImplicit false

open KeskinZeevi.SufficientConditions

namespace L894

open CVPricing.Regret Filter Topology Set

/-- the derivative of the revenue in the price -/
noncomputable def G (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) : ℝ :=
  M.h (a.1 + a.2 * p) + p * (deriv M.h (a.1 + a.2 * p) * a.2)

/-- the second derivative of the revenue in the price -/
noncomputable def F (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) : ℝ :=
  2 * a.2 * deriv M.h (a.1 + a.2 * p) + p * a.2 ^ 2 * deriv (deriv M.h) (a.1 + a.2 * p)

theorem hC2 (M : CVPricing.Regret.Model) : ContDiffOn ℝ 2 M.h (Ioi 0) :=
  M.h_contDiffOn.mono Ioi_subset_Ici_self

theorem hC1 (M : CVPricing.Regret.Model) : ContDiffOn ℝ 1 (deriv M.h) (Ioi 0) :=
  (hC2 M).deriv_of_isOpen isOpen_Ioi (by norm_num)

theorem h_diff (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ M.h x :=
  ((hC2 M).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)

theorem dh_diff (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    DifferentiableAt ℝ (deriv M.h) x :=
  ((hC1 M).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by norm_num)

theorem h_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) : ContinuousAt M.h x :=
  (h_diff M x hx).continuousAt

theorem dh_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    ContinuousAt (deriv M.h) x :=
  (dh_diff M x hx).continuousAt

theorem ddh_cont (M : CVPricing.Regret.Model) (x : ℝ) (hx : 0 < x) :
    ContinuousAt (deriv (deriv M.h)) x :=
  ((hC1 M).continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).continuousAt (Ioi_mem_nhds hx)

theorem lin_hasDeriv (a : ℝ × ℝ) (p : ℝ) :
    HasDerivAt (fun q : ℝ => a.1 + a.2 * q) a.2 p := by
  have := ((hasDerivAt_id p).const_mul a.2).const_add a.1
  simpa using this

theorem rev_hasDeriv (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ)
    (hx : 0 < a.1 + a.2 * p) : HasDerivAt (revenue M.h a) (G M a p) p := by
  have h1 : HasDerivAt (fun q : ℝ => M.h (a.1 + a.2 * q)) (deriv M.h (a.1 + a.2 * p) * a.2) p :=
    (h_diff M _ hx).hasDerivAt.comp p (lin_hasDeriv a p)
  have h2 := (hasDerivAt_id p).mul h1
  have e : revenue M.h a = fun q : ℝ => id q * M.h (a.1 + a.2 * q) := by
    funext q; simp [CVPricing.Regret.revenue]
  rw [e]
  refine h2.congr_deriv ?_
  unfold G
  simp only [id_eq]
  ring

theorem G_hasDeriv (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ)
    (hx : 0 < a.1 + a.2 * p) : HasDerivAt (fun q => G M a q) (F M a p) p := by
  have h1 : HasDerivAt (fun q : ℝ => M.h (a.1 + a.2 * q)) (deriv M.h (a.1 + a.2 * p) * a.2) p :=
    (h_diff M _ hx).hasDerivAt.comp p (lin_hasDeriv a p)
  have h3 : HasDerivAt (fun q : ℝ => deriv M.h (a.1 + a.2 * q))
      (deriv (deriv M.h) (a.1 + a.2 * p) * a.2) p :=
    by
      have hd : HasDerivAt (deriv M.h) (deriv (deriv M.h) (a.1 + a.2 * p)) (a.1 + a.2 * p) :=
        (dh_diff M _ hx).hasDerivAt
      exact hd.comp p (lin_hasDeriv a p)
  have h4 := (hasDerivAt_id p).mul (h3.mul_const a.2)
  have h5 := h1.add h4
  have e : (fun q => G M a q) =
      fun q : ℝ => M.h (a.1 + a.2 * q) + id q * (deriv M.h (a.1 + a.2 * q) * a.2) := by
    funext q; unfold G; simp only [id_eq]
  rw [e]
  refine h5.congr_deriv ?_
  unfold F
  simp only [id_eq]
  ring

theorem d2_eq (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (p : ℝ) (hx : 0 < a.1 + a.2 * p) :
    deriv (deriv (revenue M.h a)) p = F M a p := by
  have hc : Continuous fun q : ℝ => a.1 + a.2 * q := by fun_prop
  have hev : ∀ᶠ q in 𝓝 p, 0 < a.1 + a.2 * q := (hc.tendsto p).eventually_const_lt hx
  have heq : deriv (revenue M.h a) =ᶠ[𝓝 p] fun q => G M a q :=
    hev.mono fun q hq => (rev_hasDeriv M a q hq).deriv
  rw [heq.deriv_eq]
  exact (G_hasDeriv M a p hx).deriv

theorem rev_cont (M : CVPricing.Regret.Model) (z : ℝ × (ℝ × ℝ)) (hz : 0 < z.2.1 + z.2.2 * z.1) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => revenue M.h z.2 z.1) z := by
  have hin : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.1 + z.2.2 * z.1) z := by fun_prop
  have hh : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => M.h (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := M.h) (h_cont M _ hz) hin
  exact continuousAt_fst.mul hh

theorem F_cont (M : CVPricing.Regret.Model) (z : ℝ × (ℝ × ℝ)) (hz : 0 < z.2.1 + z.2.2 * z.1) :
    ContinuousAt (fun z : ℝ × (ℝ × ℝ) => F M z.2 z.1) z := by
  have hin : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.1 + z.2.2 * z.1) z := by fun_prop
  have h1 : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => deriv M.h (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := deriv M.h) (dh_cont M _ hz) hin
  have h2 : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => deriv (deriv M.h) (z.2.1 + z.2.2 * z.1)) z :=
    ContinuousAt.comp (g := deriv (deriv M.h)) (ddh_cont M _ hz) hin
  have hs : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.2.2) z := by fun_prop
  have hf : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => z.1) z := by fun_prop
  exact ((continuousAt_const.mul hs).mul h1).add ((hf.mul (hs.pow 2)).mul h2)

theorem rev_lim (M : CVPricing.Regret.Model) (A : ℕ → ℝ × ℝ) (P : ℕ → ℝ) (a : ℝ × ℝ) (p : ℝ)
    (hA : Tendsto A atTop (𝓝 a)) (hP : Tendsto P atTop (𝓝 p)) (hz : 0 < a.1 + a.2 * p) :
    Tendsto (fun k => revenue M.h (A k) (P k)) atTop (𝓝 (revenue M.h a p)) := by
  have := (rev_cont M (p, a) hz).tendsto.comp (hP.prodMk_nhds hA)
  exact this

theorem opt_eq (M : CVPricing.Regret.Model) (a : ℝ × ℝ) (q : ℝ) (hq : q ∈ Icc M.pl M.ph)
    (hs : ∀ q' ∈ Icc M.pl M.ph, q' ≠ q → revenue M.h a q' < revenue M.h a q) :
    optPriceOf M a = q := by
  have hmax : ∀ q' ∈ Icc M.pl M.ph, revenue M.h a q' ≤ revenue M.h a q := by
    intro q' hq'
    by_cases h : q' = q
    · rw [h]
    · exact (hs q' hq' h).le
  have hex : ∃ q1, ∀ q', IsRevMaxOn M a (Icc M.pl M.ph) q' ↔ q' = q1 := by
    refine ⟨q, fun q' => ⟨fun h => ?_, fun h => ?_⟩⟩
    · by_contra hne
      have := hs q' h.1 hne
      have := h.2 q hq
      linarith
    · subst h
      exact ⟨hq, hmax⟩
  unfold optPriceOf
  rw [dif_pos hex]
  exact ((Classical.choose_spec hex q).1 ⟨hq, hmax⟩).symm

theorem optU (M : CVPricing.Regret.Model) (U : Set (ℝ × ℝ))
    (hU : ∀ a ∈ U, ∃ q ∈ Ioo M.pl M.ph,
      (∀ q' ∈ Icc M.pl M.ph, q' ≠ q → revenue M.h a q' < revenue M.h a q) ∧
      deriv (deriv (revenue M.h a)) q < 0) (a : ℝ × ℝ) (ha : a ∈ U) :
    optPriceOf M a ∈ Ioo M.pl M.ph ∧
      ∀ q' ∈ Icc M.pl M.ph, q' ≠ optPriceOf M a →
        revenue M.h a q' < revenue M.h a (optPriceOf M a) := by
  obtain ⟨q, hq, hs, -⟩ := hU a ha
  rw [opt_eq M a q (Ioo_subset_Icc_self hq) hs]
  exact ⟨hq, hs⟩

theorem euclid_le (a b : ℝ × ℝ) : dist a b ≤ euclidNorm (a - b) := by
  have h1 : |a.1 - b.1| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.2 - b.2)])
  have h2 : |a.2 - b.2| ≤ euclidNorm (a - b) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.1 - b.1)])
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le h1 h2

theorem qgrowth (f g g' : ℝ → ℝ) (pl ph p0 : ℝ) (hp0 : p0 ∈ Ioo pl ph) (W : Set ℝ)
    (hW : IsOpen W) (hIW : Icc pl ph ⊆ W) (hf : ∀ x ∈ W, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ W, HasDerivAt g (g' x) x) (hc : ContinuousAt g' p0) (hneg : g' p0 < 0)
    (hs : ∀ q ∈ Icc pl ph, q ≠ p0 → f q < f p0) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ Icc pl ph, c * (p - p0) ^ 2 ≤ f p0 - f p := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = -g' p0 / 2 := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hev1 : ∀ᶠ x in 𝓝 p0, g' x < -κ :=
    Filter.Tendsto.eventually_lt_const (by rw [hκdef]; linarith) hc
  have hp0W : p0 ∈ W := hIW (Ioo_subset_Icc_self hp0)
  have hev2 : W ∈ 𝓝 p0 := hW.mem_nhds hp0W
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hev1.and hev2)
  have hg0 : g p0 = 0 := by
    have hloc : IsLocalMax f p0 := by
      filter_upwards [Icc_mem_nhds hp0.1 hp0.2] with q hq
      by_cases h : q = p0
      · rw [h]
      · exact (hs q hq h).le
    exact hloc.hasDerivAt_eq_zero (hf p0 hp0W)
  have inB : ∀ x, |x - p0| < δ → g' x < -κ ∧ x ∈ W := fun x hx =>
    hball (by rw [Real.dist_eq]; exact hx)
  have hψd : ∀ x ∈ W, HasDerivAt (fun y => g y + κ * (y - p0)) (g' x + κ) x := by
    intro x hx
    have := (hg x hx).add (((hasDerivAt_id x).sub_const p0).const_mul κ)
    refine this.congr_deriv ?_
    simp
  have hφd : ∀ x ∈ W, HasDerivAt (fun y => f y + κ / 2 * (y - p0) ^ 2)
      (g x + κ * (x - p0)) x := by
    intro x hx
    have h2 : HasDerivAt (fun y => (y - p0) ^ 2) (2 * (x - p0)) x := by
      have := ((hasDerivAt_id x).sub_const p0).pow 2
      refine this.congr_deriv ?_
      simp
    have := (hf x hx).add (h2.const_mul (κ / 2))
    refine this.congr_deriv ?_
    ring
  have hψanti : AntitoneOn (fun y => g y + κ * (y - p0)) (Metric.ball p0 δ) := by
    have hB : ∀ x ∈ Metric.ball p0 δ, g' x < -κ ∧ x ∈ W := fun x hx =>
      inB x (by rw [Metric.mem_ball, Real.dist_eq] at hx; exact hx)
    apply antitoneOn_of_deriv_nonpos (convex_ball p0 δ)
    · intro x hx; exact (hψd x (hB x hx).2).continuousAt.continuousWithinAt
    · rw [Metric.isOpen_ball.interior_eq]
      intro x hx; exact (hψd x (hB x hx).2).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [Metric.isOpen_ball.interior_eq] at hx
      rw [(hψd x (hB x hx).2).deriv]
      linarith [(hB x hx).1]
  have memB : ∀ x, |x - p0| < δ → x ∈ Metric.ball p0 δ := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq]; exact hx
  have hψ0 : g p0 + κ * (p0 - p0) = 0 := by rw [hg0]; ring
  have hloc : ∀ p, |p - p0| < δ → κ / 2 * (p - p0) ^ 2 ≤ f p0 - f p := by
    intro p hp
    have hp' := abs_lt.1 hp
    rcases le_total p0 p with h | h
    · have hsub : ∀ x ∈ Icc p0 p, |x - p0| < δ := fun x hx =>
        abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hA : AntitoneOn (fun y => f y + κ / 2 * (y - p0) ^ 2) (Icc p0 p) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc p0 p)
        · intro x hx; exact (hφd x (inB x (hsub x hx)).2).continuousAt.continuousWithinAt
        · rw [interior_Icc]
          intro x hx
          exact (hφd x (inB x (hsub x (Ioo_subset_Icc_self hx))).2).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro x hx
          have hxI := Ioo_subset_Icc_self hx
          rw [(hφd x (inB x (hsub x hxI)).2).deriv]
          have := hψanti (memB p0 (by simpa using hδ)) (memB x (hsub x hxI)) hx.1.le
          simp only at this
          linarith
      have := hA (left_mem_Icc.2 h) (right_mem_Icc.2 h) h
      simp only [sub_self] at this
      linarith
    · have hsub : ∀ x ∈ Icc p p0, |x - p0| < δ := fun x hx =>
        abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
      have hA : MonotoneOn (fun y => f y + κ / 2 * (y - p0) ^ 2) (Icc p p0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc p p0)
        · intro x hx; exact (hφd x (inB x (hsub x hx)).2).continuousAt.continuousWithinAt
        · rw [interior_Icc]
          intro x hx
          exact (hφd x (inB x (hsub x (Ioo_subset_Icc_self hx))).2).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro x hx
          have hxI := Ioo_subset_Icc_self hx
          rw [(hφd x (inB x (hsub x hxI)).2).deriv]
          have := hψanti (memB x (hsub x hxI)) (memB p0 (by simpa using hδ)) hx.2.le
          simp only at this
          linarith
      have := hA (left_mem_Icc.2 h) (right_mem_Icc.2 h) h
      simp only [sub_self] at this
      linarith
  -- global gap
  have hfc : ContinuousOn f (Icc pl ph) := fun x hx => (hf x (hIW hx)).continuousAt.continuousWithinAt
  obtain ⟨γ, hγ, hgap⟩ : ∃ γ : ℝ, 0 < γ ∧ ∀ p ∈ Icc pl ph, δ ≤ |p - p0| → f p ≤ f p0 - γ := by
    set K := Icc pl ph ∩ {p | δ ≤ |p - p0|} with hK
    rcases K.eq_empty_or_nonempty with hE | hN
    · refine ⟨1, one_pos, fun p hp hd => ?_⟩
      have : p ∈ K := ⟨hp, hd⟩
      rw [hE] at this
      exact absurd this (Set.notMem_empty p)
    · have hKc : IsCompact K :=
        isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
      obtain ⟨pm, hpm, hmax⟩ := hKc.exists_isMaxOn hN (hfc.mono inter_subset_left)
      have hne : pm ≠ p0 := by
        intro h
        have := hpm.2
        simp only [mem_ofPred_eq, h, sub_self, abs_zero] at this
        linarith
      have hlt := hs pm hpm.1 hne
      refine ⟨f p0 - f pm, by linarith, fun p hp hd => ?_⟩
      have := hmax ⟨hp, hd⟩
      simp only [mem_ofPred_eq] at this
      linarith
  have hL : 0 < ph - pl := by linarith [hp0.1, hp0.2]
  refine ⟨min (κ / 2) (γ / (ph - pl) ^ 2), lt_min (by linarith) (by positivity), ?_⟩
  intro p hp
  have hsq : (p - p0) ^ 2 ≤ (ph - pl) ^ 2 := by
    have h1 : |p - p0| ≤ ph - pl := abs_le.2 ⟨by linarith [hp.1, hp0.2], by linarith [hp.2, hp0.1]⟩
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rcases lt_or_ge |p - p0| δ with hd | hd
  · have := hloc p hd
    have : min (κ / 2) (γ / (ph - pl) ^ 2) * (p - p0) ^ 2 ≤ κ / 2 * (p - p0) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    linarith
  · have h1 := hgap p hp hd
    have h2 : min (κ / 2) (γ / (ph - pl) ^ 2) * (p - p0) ^ 2 ≤ γ / (ph - pl) ^ 2 * (p - p0) ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    have h3 : γ / (ph - pl) ^ 2 * (p - p0) ^ 2 ≤ γ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith

theorem gbound (hx hy dhx dhy a2 b2 p e K1 K2 ph dx L : ℝ) (hLd : L = K1 * (1 + ph) + ph * (K1 + K2 * (1 + ph) * |b2|))
    (hdx : |dx| ≤ (1 + ph) * e) (h1 : |hx - hy| ≤ K1 * |dx|) (h2 : |dhx| ≤ K1)
    (h3 : |dhx - dhy| ≤ K2 * |dx|) (h4 : |a2 - b2| ≤ e) (hp0 : 0 ≤ p) (hp : p ≤ ph)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    |(hx + p * (dhx * a2)) - (hy + p * (dhy * b2))| ≤ L * e := by
  subst hLd
  have e1 : (hx + p * (dhx * a2)) - (hy + p * (dhy * b2)) =
      (hx - hy) + p * (dhx * (a2 - b2) + (dhx - dhy) * b2) := by ring
  rw [e1]
  have t1 : |hx - hy| ≤ K1 * ((1 + ph) * e) := h1.trans (mul_le_mul_of_nonneg_left hdx hK1)
  have t2 : |dhx * (a2 - b2)| ≤ K1 * e := by
    rw [abs_mul]; exact mul_le_mul h2 h4 (abs_nonneg _) hK1
  have t3 : |(dhx - dhy) * b2| ≤ K2 * ((1 + ph) * e) * |b2| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (h3.trans (mul_le_mul_of_nonneg_left hdx hK2)) (abs_nonneg _)
  have t4 : |dhx * (a2 - b2) + (dhx - dhy) * b2| ≤ K1 * e + K2 * ((1 + ph) * e) * |b2| :=
    (abs_add_le _ _).trans (add_le_add t2 t3)
  have t5 : |p * (dhx * (a2 - b2) + (dhx - dhy) * b2)| ≤
      ph * (K1 * e + K2 * ((1 + ph) * e) * |b2|) := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact mul_le_mul hp t4 (abs_nonneg _) (hp0.trans hp)
  calc _ ≤ |hx - hy| + |p * (dhx * (a2 - b2) + (dhx - dhy) * b2)| := abs_add_le _ _
    _ ≤ K1 * ((1 + ph) * e) + ph * (K1 * e + K2 * ((1 + ph) * e) * |b2|) := add_le_add t1 t5
    _ = _ := by ring

theorem main (M : CVPricing.Regret.Model) :
    ∃ V ∈ 𝓝 M.a0, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ V,
      |optPriceOf M a - pOpt M| ≤ C * euclidNorm (a - M.a0) := by
  obtain ⟨U, hUo, hbU, hU⟩ := M.nbhd
  obtain ⟨p0, hp0, hs0, hd0⟩ := hU M.a0 hbU
  have hpO : pOpt M = p0 := opt_eq M M.a0 p0 (Ioo_subset_Icc_self hp0) hs0
  have hb2 : M.a0.2 < 0 := M.a01_neg
  have hbph : 0 < M.a0.1 + M.a0.2 * M.ph := M.a0_ph_pos
  have hpl := M.pl_pos
  have hplph := M.pl_lt_ph
  have hargb : ∀ p, p ≤ M.ph → M.a0.1 + M.a0.2 * M.ph ≤ M.a0.1 + M.a0.2 * p := fun p hp => by
    nlinarith
  have hWo : IsOpen {p : ℝ | 0 < M.a0.1 + M.a0.2 * p} := isOpen_lt continuous_const (by fun_prop)
  have hIW : Icc M.pl M.ph ⊆ {p : ℝ | 0 < M.a0.1 + M.a0.2 * p} := fun p hp =>
    lt_of_lt_of_le hbph (hargb p hp.2)
  have hp0W : 0 < M.a0.1 + M.a0.2 * p0 := hIW (Ioo_subset_Icc_self hp0)
  have hFc : ContinuousAt (F M M.a0) p0 := by
    have h1 := F_cont M (p0, M.a0) hp0W
    have h2 : ContinuousAt (fun p : ℝ => (p, M.a0)) p0 := by fun_prop
    have h3 : ContinuousAt ((fun z : ℝ × (ℝ × ℝ) => F M z.2 z.1) ∘ (fun p : ℝ => (p, M.a0))) p0 :=
      ContinuousAt.comp (f := fun p : ℝ => (p, M.a0)) h1 h2
    exact h3
  obtain ⟨c, hc, hqg⟩ := qgrowth (revenue M.h M.a0) (G M M.a0) (F M M.a0) M.pl M.ph p0 hp0 _ hWo
    hIW (fun x hx => rev_hasDeriv M M.a0 x hx) (fun x hx => G_hasDeriv M M.a0 x hx) hFc
    (by rw [← d2_eq M M.a0 p0 hp0W]; exact hd0) hs0
  obtain ⟨α, hαd⟩ : ∃ α : ℝ, α = (M.a0.1 + M.a0.2 * M.ph) / 2 := ⟨_, rfl⟩
  obtain ⟨β, hβd⟩ : ∃ β : ℝ, β = M.a0.1 + M.a0.2 * M.pl + α := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hαd]; linarith
  have hIpos : ∀ x ∈ Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hdhc : ContinuousOn (deriv M.h) (Icc α β) := fun x hx =>
    (dh_cont M x (hIpos x hx)).continuousWithinAt
  have hddhc : ContinuousOn (deriv (deriv M.h)) (Icc α β) := fun x hx =>
    (ddh_cont M x (hIpos x hx)).continuousWithinAt
  obtain ⟨K1', hK1'⟩ := isCompact_Icc.exists_bound_of_continuousOn hdhc
  obtain ⟨K2', hK2'⟩ := isCompact_Icc.exists_bound_of_continuousOn hddhc
  have hK1 : (0 : ℝ) ≤ max K1' 0 := le_max_right _ _
  have hK2 : (0 : ℝ) ≤ max K2' 0 := le_max_right _ _
  have hb1 : ∀ x ∈ Icc α β, |deriv M.h x| ≤ max K1' 0 := fun x hx => by
    have := hK1' x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hb2' : ∀ x ∈ Icc α β, |deriv (deriv M.h) x| ≤ max K2' 0 := fun x hx => by
    have := hK2' x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have hLip1 : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β, |M.h x - M.h y| ≤ max K1' 0 * |x - y| := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := M.h)
      (fun z hz => h_diff M z (hIpos z hz)) (fun z hz => by rw [Real.norm_eq_abs]; exact hb1 z hz)
      (convex_Icc α β) hy hx
    simpa only [Real.norm_eq_abs] using this
  have hLip2 : ∀ x ∈ Icc α β, ∀ y ∈ Icc α β,
      |deriv M.h x - deriv M.h y| ≤ max K2' 0 * |x - y| := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv M.h)
      (fun z hz => dh_diff M z (hIpos z hz)) (fun z hz => by rw [Real.norm_eq_abs]; exact hb2' z hz)
      (convex_Icc α β) hy hx
    simpa only [Real.norm_eq_abs] using this
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = max K1' 0 * (1 + M.ph) +
      M.ph * (max K1' 0 + max K2' 0 * (1 + M.ph) * |M.a0.2|) := ⟨_, rfl⟩
  have hL : 0 ≤ L := by
    rw [hLd]
    exact add_nonneg (mul_nonneg hK1 (by linarith)) (mul_nonneg (by linarith)
      (add_nonneg hK1 (mul_nonneg (mul_nonneg hK2 (by linarith)) (abs_nonneg _))))
  have h1ph : 0 < 1 + M.ph := by linarith
  obtain ⟨ε, hεd⟩ : ∃ ε : ℝ, ε = α / (1 + M.ph) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεd]; positivity
  have hεα : ε * (1 + M.ph) = α := by rw [hεd]; field_simp
  refine ⟨U ∩ Metric.ball M.a0 ε, Filter.inter_mem (hUo.mem_nhds hbU) (Metric.ball_mem_nhds _ hε),
    (L + 1) / c, by positivity, ?_⟩
  rintro a ⟨haU, hab⟩
  have he : 0 ≤ euclidNorm (a - M.a0) := Real.sqrt_nonneg _
  have he1 : |a.1 - M.a0.1| ≤ euclidNorm (a - M.a0) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.2 - M.a0.2)])
  have he2 : |a.2 - M.a0.2| ≤ euclidNorm (a - M.a0) :=
    Real.abs_le_sqrt (by simp only [Prod.fst_sub, Prod.snd_sub]; nlinarith [sq_nonneg (a.1 - M.a0.1)])
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff] at hab
  obtain ⟨hd1, hd2⟩ := hab
  have hargs : ∀ p ∈ Icc M.pl M.ph, (M.a0.1 + M.a0.2 * p ∈ Icc α β) ∧
      (a.1 + a.2 * p ∈ Icc α β) ∧
      |(a.1 + a.2 * p) - (M.a0.1 + M.a0.2 * p)| ≤ (1 + M.ph) * euclidNorm (a - M.a0) := by
    intro p hp
    have hp0' : 0 ≤ p := hpl.le.trans hp.1
    have hbp1 : 2 * α ≤ M.a0.1 + M.a0.2 * p := by rw [hαd]; linarith [hargb p hp.2]
    have hbp2 : M.a0.1 + M.a0.2 * p ≤ M.a0.1 + M.a0.2 * M.pl := by nlinarith [hp.1]
    have hdx : |(a.1 + a.2 * p) - (M.a0.1 + M.a0.2 * p)| ≤
        |a.1 - M.a0.1| + |a.2 - M.a0.2| * p := by
      have : (a.1 + a.2 * p) - (M.a0.1 + M.a0.2 * p) = (a.1 - M.a0.1) + (a.2 - M.a0.2) * p := by ring
      rw [this]
      calc _ ≤ |a.1 - M.a0.1| + |(a.2 - M.a0.2) * p| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hp0']
    have hm1 : |a.2 - M.a0.2| * p ≤ ε * M.ph := mul_le_mul hd2.le hp.2 hp0' hε.le
    have hm2 : |a.2 - M.a0.2| * p ≤ euclidNorm (a - M.a0) * M.ph := mul_le_mul he2 hp.2 hp0' he
    have hdα : |(a.1 + a.2 * p) - (M.a0.1 + M.a0.2 * p)| ≤ α := by
      have : |a.1 - M.a0.1| + |a.2 - M.a0.2| * p ≤ ε * (1 + M.ph) := by nlinarith
      linarith
    have hab' := abs_le.1 hdα
    refine ⟨⟨by linarith, by rw [hβd]; linarith⟩, ⟨by linarith, by rw [hβd]; linarith⟩, ?_⟩
    nlinarith
  have hD : ∀ x ∈ Icc M.pl M.ph, ∀ y ∈ Icc M.pl M.ph,
      |(revenue M.h a x - revenue M.h M.a0 x) - (revenue M.h a y - revenue M.h M.a0 y)| ≤
        (L * euclidNorm (a - M.a0)) * |x - y| := by
    intro x hx y hy
    have hdiff : ∀ z ∈ Icc M.pl M.ph, HasDerivAt (fun p => revenue M.h a p - revenue M.h M.a0 p)
        (G M a z - G M M.a0 z) z := fun z hz =>
      (rev_hasDeriv M a z (hIpos _ (hargs z hz).2.1)).sub
        (rev_hasDeriv M M.a0 z (hIpos _ (hargs z hz).1))
    have hbd : ∀ z ∈ Icc M.pl M.ph, |G M a z - G M M.a0 z| ≤ L * euclidNorm (a - M.a0) := by
      intro z hz
      obtain ⟨hzb, hza, hzd⟩ := hargs z hz
      unfold G
      exact gbound _ _ _ _ a.2 M.a0.2 z _ (max K1' 0) (max K2' 0) M.ph _ L hLd hzd
        (hLip1 _ hza _ hzb) (hb1 _ hza) (hLip2 _ hza _ hzb) he2 (hpl.le.trans hz.1) hz.2 hK1 hK2
    have := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun p => revenue M.h a p - revenue M.h M.a0 p) (C := L * euclidNorm (a - M.a0))
      (fun z hz => (hdiff z hz).differentiableAt)
      (fun z hz => by rw [(hdiff z hz).deriv, Real.norm_eq_abs]; exact hbd z hz)
      (convex_Icc _ _) hy hx
    simpa only [Real.norm_eq_abs] using this
  obtain ⟨hqI, hqs⟩ := optU M U hU a haU
  have hrq : revenue M.h a p0 ≤ revenue M.h a (optPriceOf M a) := by
    by_cases h : p0 = optPriceOf M a
    · rw [h]
    · exact (hqs p0 (Ioo_subset_Icc_self hp0) h).le
  have hg := hqg (optPriceOf M a) (Ioo_subset_Icc_self hqI)
  have hDq := hD (optPriceOf M a) (Ioo_subset_Icc_self hqI) p0 (Ioo_subset_Icc_self hp0)
  rw [hpO]
  have hle := le_abs_self ((revenue M.h a (optPriceOf M a) - revenue M.h M.a0 (optPriceOf M a)) -
    (revenue M.h a p0 - revenue M.h M.a0 p0))
  have key : c * |optPriceOf M a - p0| * |optPriceOf M a - p0| ≤
      L * euclidNorm (a - M.a0) * |optPriceOf M a - p0| := by
    have : c * |optPriceOf M a - p0| * |optPriceOf M a - p0| = c * (optPriceOf M a - p0) ^ 2 := by
      rw [mul_assoc, ← sq, sq_abs]
    rw [this]
    linarith
  have key2 : c * |optPriceOf M a - p0| ≤ L * euclidNorm (a - M.a0) := by
    rcases (abs_nonneg (optPriceOf M a - p0)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; positivity
    · exact le_of_mul_le_mul_right key hpos
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

end L894

open CVPricing.Regret KeskinZeevi.SufficientConditions in
theorem solution (M : CVPricing.Regret.Model) :
    ∃ V ∈ nhds M.a0, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ V,
      |optPriceOf M a - pOpt M| ≤ C * euclidNorm (a - M.a0) := by
  exact L894.main M
