-- Prove2me | solution 1 for EpiControl.SinglePeak.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:08:59.869595+00:00
-- url     : https://prove2.me/submissions/7028f55c-9eea-4e09-8014-7d40e9aa64b8

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiAuxL10

lemma exp_lipschitzOnWith_Iic (M : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp M)) Real.exp (Iic M) := by
  apply (convex_Iic M).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => Real.differentiableAt_exp)
  intro x hx
  rw [Real.deriv_exp]
  have : ‖Real.exp x‖₊ = Real.toNNReal (Real.exp x) := by
    ext; simp [abs_of_pos (Real.exp_pos x), (Real.exp_pos x).le]
  rw [this]
  exact Real.toNNReal_le_toNNReal (Real.exp_le_exp.mpr hx)

/-- Linear integral equation `x(t) = x0 + ∫₀ᵗ k x` has the exponential solution. -/
theorem lin_eq_exp {T x0 K : ℝ} (hT : 0 ≤ T) {k x : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hkb : ∀ r ∈ Icc 0 T, |k r| ≤ K)
    (hx : ContinuousOn x (Icc 0 T))
    (heq : ∀ t ∈ Icc 0 T, x t = x0 + ∫ r in (0:ℝ)..t, k r * x r) :
    ∀ t ∈ Icc 0 T, x t = x0 * Real.exp (∫ r in (0:ℝ)..t, k r) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hkb 0 ⟨le_rfl, hT⟩)
  have huIcc : uIcc 0 T = Icc 0 T := uIcc_of_le hT
  set A : ℝ → ℝ := fun t => ∫ r in (0:ℝ)..t, k r with hA
  have hkx : IntervalIntegrable (fun r => k r * x r) volume 0 T :=
    hk.mul_continuousOn (by rw [huIcc]; exact hx)
  have hkI : ∀ t ∈ Icc 0 T, IntervalIntegrable k volume 0 t := fun t ht =>
    hk.mono_set (by rw [huIcc, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  -- A is K-Lipschitz on [0,T]
  have hAL : LipschitzOnWith (Real.toNNReal K) A (Icc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hK]
    have : A t - A u = ∫ r in u..t, k r := by
      simp only [hA]; exact intervalIntegral.integral_interval_sub_left (hkI t ht) (hkI u hu)
    rw [this, ← Real.norm_eq_abs]
    calc ‖∫ r in u..t, k r‖ ≤ K * |t - u| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro r hr
          rw [Real.norm_eq_abs]
          apply hkb
          have := uIoc_subset_uIcc hr
          rw [mem_uIcc] at this
          rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
            linarith [ht.1, ht.2, hu.1, hu.2]
      _ = K * |t - u| := rfl
  have hAb : ∀ t ∈ Icc 0 T, -A t ≤ K * T := by
    intro t ht
    have h0 : A 0 = 0 := by simp [hA]
    have := hAL.dist_le_mul t ht 0 ⟨le_rfl, hT⟩
    rw [Real.dist_eq, Real.dist_eq, h0, Real.coe_toNNReal _ hK, sub_zero, sub_zero,
      abs_of_nonneg ht.1] at this
    have h2 := neg_abs_le (A t)
    nlinarith [ht.2]
  set E : ℝ → ℝ := fun t => Real.exp (-A t) with hE
  have hEL : LipschitzOnWith (Real.toNNReal (Real.exp (K * T)) * Real.toNNReal K) E (Icc 0 T) := by
    have := (exp_lipschitzOnWith_Iic (K * T)).comp hAL.neg (fun t ht => hAb t ht)
    exact this
  set x' : ℝ → ℝ := fun t => x0 + ∫ r in (0:ℝ)..t, k r * x r with hx'
  have hx'AC : AbsolutelyContinuousOnInterval x' 0 T := by
    have h1 := hkx.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
    have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => x0) 0 T :=
      (LipschitzWith.const x0).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h2.fun_add h1
  have hEAC : AbsolutelyContinuousOnInterval E 0 T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [huIcc]; exact hEL
  have hFAC : AbsolutelyContinuousOnInterval (fun t => x' t * E t) 0 T := hx'AC.fun_mul hEAC
  have hderiv : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun t => x' t * E t) 0 t := by
    filter_upwards [hkx.ae_hasDerivAt_integral, hk.ae_hasDerivAt_integral] with t h1 h2 ht
    have d1 : HasDerivAt x' (k t * x t) t := (h1 ht 0 (by simp)).const_add x0
    have d2 : HasDerivAt A (k t) t := h2 ht 0 (by simp)
    have d3 : HasDerivAt E (Real.exp (-A t) * -k t) t := (d2.neg).exp
    rw [huIcc] at ht
    have hxx : x t = x' t := heq t ht
    refine (d1.fun_mul d3).congr_deriv ?_
    rw [hxx]; simp only [hE]; ring
  obtain ⟨C, hC⟩ := hFAC.const_of_ae_hasDerivAt_zero hderiv
  intro t ht
  have h0 := hC 0 (by simp)
  have ht' := hC t (by rw [huIcc]; exact ht)
  have hx'0 : x' 0 = x0 := by simp [hx']
  have hE0 : E 0 = 1 := by simp [hE, hA]
  rw [hx'0, hE0, mul_one] at h0
  rw [heq t ht]
  change x' t = x0 * Real.exp (A t)
  have hEt : E t * Real.exp (A t) = 1 := by
    simp only [hE]; rw [← Real.exp_add]; simp
  calc x' t = x' t * E t * Real.exp (A t) := by rw [mul_assoc, hEt, mul_one]
    _ = x0 * Real.exp (A t) := by rw [ht', h0]


open EpiControl.SinglePeak in
/-- Exponential representation of the SIR path. -/
theorem path_exp {P : Params} (hP : P.Standing) {β s i : ℝ → ℝ} (hβ : P.Admissible β)
    (hpath : P.IsSIRPath β s i) :
    IntervalIntegrable β volume 0 P.T ∧
    (∀ t ∈ Icc 0 P.T, i t = P.i0 * Real.exp (∫ r in (0:ℝ)..t, (β r * s r - P.γ))) ∧
    (∀ t ∈ Icc 0 P.T, s t = P.s0 * Real.exp (∫ r in (0:ℝ)..t, -(β r * i r))) := by
  have hT : 0 ≤ P.T := hP.T_pos.le
  obtain ⟨hs, hi, heq⟩ := hpath
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  have hβb : ∀ r ∈ Icc 0 P.T, |β r| ≤ P.bbar := by
    intro r hr
    have := hβ.2 r hr
    rw [abs_of_pos (lt_of_lt_of_le hP.bl_pos this.1)]; exact this.2
  have hβI : IntervalIntegrable β volume 0 P.T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    refine Measure.integrableOn_of_bounded (M := P.bbar) (by simp) hβ.1.aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => by
      rw [Real.norm_eq_abs]; exact hβb r hr)
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hs
  obtain ⟨I, hI⟩ := isCompact_Icc.exists_bound_of_continuousOn hi
  have hS0 : 0 ≤ S := le_trans (norm_nonneg _) (hS 0 ⟨le_rfl, hT⟩)
  have hI0 : 0 ≤ I := le_trans (norm_nonneg _) (hI 0 ⟨le_rfl, hT⟩)
  have hbb : 0 ≤ P.bbar := (hP.bl_pos.trans hP.bl_lt_bbar).le
  refine ⟨hβI, ?_, ?_⟩
  · apply lin_eq_exp hT (K := P.bbar * S + |P.γ|)
    · exact (hβI.mul_continuousOn (by rw [huIcc]; exact hs)).sub intervalIntegrable_const
    · intro r hr
      calc |β r * s r - P.γ| ≤ |β r * s r| + |P.γ| := abs_sub _ _
        _ ≤ P.bbar * S + |P.γ| := by
          rw [abs_mul]
          have := hS r hr; rw [Real.norm_eq_abs] at this
          gcongr
          · exact hβb r hr
    · exact hi
    · intro t ht
      rw [(heq t ht).2]
      congr 1
      apply intervalIntegral.integral_congr
      intro r _; simp only; ring
  · apply lin_eq_exp hT (K := P.bbar * I)
    · exact (hβI.mul_continuousOn (by rw [huIcc]; exact hi)).neg
    · intro r hr
      rw [abs_neg, abs_mul]
      have := hI r hr; rw [Real.norm_eq_abs] at this
      gcongr
      exact hβb r hr
    · exact hs
    · intro t ht
      rw [(heq t ht).1, sub_eq_add_neg]
      congr 1
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro r _; simp only; ring

end EpiAuxL10



open EpiControl.SinglePeak in
/-- If `y ≤ K`-small, every minimiser lies above `b1`. -/
theorem EpiAuxL10.argmin_ge {P : Params} (hP : P.Standing) {y b b1 : ℝ}
    (hb1 : b1 ∈ Ico P.bl P.bbar) (hy : y < P.c b1 / (P.bbar - P.bl)) (h : P.ArgminAt y b) :
    b1 ≤ b := by
  by_contra hlt
  push Not at hlt
  have hbB := h.1
  have hgap : 0 < P.bbar - P.bl := sub_pos.2 hP.bl_lt_bbar
  have hmin := h.2 P.bbar ⟨hP.bl_lt_bbar.le, le_rfl⟩
  rw [hP.c_bbar, add_zero] at hmin
  have hcb : P.c b1 ≤ P.c b := hP.c_antitone hbB ⟨hb1.1, hb1.2.le⟩ hlt.le
  have hc1 : 0 < P.c b1 := hP.c_pos b1 hb1
  -- c b ≤ y (bbar - b)
  have h1 : P.c b ≤ y * (P.bbar - b) := by linarith
  rcases le_or_gt y 0 with hy0 | hy0
  · have : y * (P.bbar - b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hy0 (by linarith [hb1.2])
    linarith
  · have h2 : y * (P.bbar - b) ≤ y * (P.bbar - P.bl) :=
      mul_le_mul_of_nonneg_left (by linarith [hbB.1]) hy0.le
    have h3 : y * (P.bbar - P.bl) < P.c b1 := by
      rwa [lt_div_iff₀ hgap] at hy
    linarith

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (lam1 lam2 : ℝ → ℝ)
    (hlam : P.IsMultiplier β s i lam1 lam2)
    (h12 : ∀ t ∈ Icc 0 P.T, P.ArgminAt ((lam2 t - lam1 t) * i t * s t) (β t))
    (t0 : ℝ) (ht0 : t0 ∈ Icc 0 P.T) (hη : lam2 t0 - lam1 t0 ≤ 0) :
    β t0 = P.bbar ∧ Tendsto β (𝓝[Icc 0 P.T] t0) (𝓝 P.bbar) := by
  obtain ⟨_, hiexp, hsexp⟩ := EpiAuxL10.path_exp hP hopt.1 hopt.2.1
  have hipos : ∀ r ∈ Icc 0 P.T, 0 < i r := fun r hr => by
    rw [hiexp r hr]; exact mul_pos hP.i0_mem.1 (Real.exp_pos _)
  have hspos : ∀ r ∈ Icc 0 P.T, 0 < s r := fun r hr => by
    rw [hsexp r hr]; exact mul_pos hP.s0_mem.1 (Real.exp_pos _)
  set y : ℝ → ℝ := fun t => (lam2 t - lam1 t) * i t * s t with hydef
  have hy0 : y t0 ≤ 0 := by
    simp only [hydef]
    have := mul_pos (hipos t0 ht0) (hspos t0 ht0)
    nlinarith
  have hycont : ContinuousOn y (Icc 0 P.T) :=
    ((hlam.2.1.sub hlam.1).mul hopt.2.1.2.1).mul hopt.2.1.1
  have hgap : 0 < P.bbar - P.bl := sub_pos.2 hP.bl_lt_bbar
  have hβB : ∀ t ∈ Icc 0 P.T, β t ∈ Icc P.bl P.bbar := fun t ht => (h12 t ht).1
  have key : ∀ b1 ∈ Ico P.bl P.bbar, ∀ᶠ t in 𝓝[Icc 0 P.T] t0, b1 ≤ β t := by
    intro b1 hb1
    have hK : 0 < P.c b1 / (P.bbar - P.bl) := div_pos (hP.c_pos b1 hb1) hgap
    have hev : ∀ᶠ t in 𝓝[Icc 0 P.T] t0, y t < P.c b1 / (P.bbar - P.bl) :=
      (hycont t0 ht0).eventually (Iio_mem_nhds (lt_of_le_of_lt hy0 hK))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htI
    exact EpiAuxL10.argmin_ge hP hb1 ht (h12 t htI)
  constructor
  · rcases (hβB t0 ht0).2.lt_or_eq with hlt | heq
    · exfalso
      have hb1 : β t0 ∈ Ico P.bl P.bbar := ⟨(hβB t0 ht0).1, hlt⟩
      have hb1' : (β t0 + P.bbar) / 2 ∈ Ico P.bl P.bbar :=
        ⟨by linarith [hb1.1], by linarith⟩
      have := EpiAuxL10.argmin_ge hP hb1'
        (lt_of_le_of_lt hy0 (div_pos (hP.c_pos _ hb1') hgap)) (h12 t0 ht0)
      linarith
    · exact heq
  · rw [tendsto_order]
    constructor
    · intro a ha
      set b1 := max P.bl ((a + P.bbar) / 2)
      have hb1 : b1 ∈ Ico P.bl P.bbar := ⟨le_max_left _ _, max_lt hP.bl_lt_bbar (by linarith)⟩
      filter_upwards [key b1 hb1] with t ht
      exact lt_of_lt_of_le (lt_of_lt_of_le (by linarith) (le_max_right _ _)) ht
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with t htI
      exact lt_of_le_of_lt (hβB t htI).2 ha
