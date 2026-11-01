-- Prove2me | solution 1 for EpiControl.SinglePeak.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:13:01.898881+00:00
-- url     : https://prove2.me/submissions/7a1b32ff-f78d-4ad0-9f18-80ef2c83455f

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model
import Theorems.Thm_EpiControl_SinglePeak_eq_33

open MeasureTheory Set Filter Topology

namespace EpiAuxL12

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

end EpiAuxL12



open EpiControl.SinglePeak in
/-- If `y ≤ K`-small, every minimiser lies above `b1`. -/
theorem EpiAuxL12.argmin_ge {P : Params} (hP : P.Standing) {y b b1 : ℝ}
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
theorem EpiAuxL12.M_eq {P : Params} {y b : ℝ} (h : P.ArgminAt y b) : P.M y = y * b + P.c b := by
  unfold Params.M
  apply IsLeast.csInf_eq
  refine ⟨⟨b, h.1, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩
  exact h.2 b' hb'

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (lam1 lam2 : ℝ → ℝ)
    (hlam : P.IsMultiplier β s i lam1 lam2) :
    ∀ t ∈ Ico 0 P.T, 0 < lam2 t - lam1 t := by
  obtain ⟨hc1, hc2, h1T, h2T, he1, he2, hargmin, h13⟩ := hlam
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hTI : P.T ∈ Icc 0 P.T := ⟨hT, le_rfl⟩
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  obtain ⟨hβI, hiexp, hsexp⟩ := EpiAuxL12.path_exp hP hopt.1 hopt.2.1
  have hs := hopt.2.1.1
  have hi := hopt.2.1.2.1
  have hipos : ∀ r ∈ Icc 0 P.T, 0 < i r := fun r hr => by
    rw [hiexp r hr]; exact mul_pos hP.i0_mem.1 (Real.exp_pos _)
  have hspos : ∀ r ∈ Icc 0 P.T, 0 < s r := fun r hr => by
    rw [hsexp r hr]; exact mul_pos hP.s0_mem.1 (Real.exp_pos _)
  have hi1 : ∀ r ∈ Icc 0 P.T, i r ≤ 1 := by
    intro r hr
    have h := ((eq_33 P hP).2 β s i hopt r hr).1
    have hs2 : 0 < s r ^ 2 := by have := hspos r hr; positivity
    have := le_of_mul_le_mul_left h hs2
    linarith [hspos r hr]
  have hdv : Continuous (deriv P.v) := hP.v_C1.continuous_deriv le_rfl
  have hvdiff : Differentiable ℝ P.v := hP.v_C1.differentiable one_ne_zero
  -- tangent inequality
  have htan : ∀ x ∈ Ioc (0:ℝ) 1, P.v x ≤ deriv P.v x * x := by
    intro x hx
    have := hP.v_convex.slope_le_deriv (x := 0) (y := x) ⟨le_rfl, zero_le_one⟩
      ⟨hx.1.le, hx.2⟩ hx.1 (hvdiff x)
    rw [slope_def_field, hP.v_zero, sub_zero, sub_zero, div_le_iff₀ hx.1] at this
    exact this
  -- positivity of the terminal values
  have hbb : 0 < P.bbar := hP.bl_pos.trans hP.bl_lt_bbar
  have hvT : 0 < P.v (i P.T) := by
    rw [← hP.v_zero]
    exact hP.v_strictMono ⟨le_rfl, zero_le_one⟩ ⟨(hipos _ hTI).le, hi1 _ hTI⟩ (hipos _ hTI)
  set MT := P.M (P.v (i P.T) * s P.T / P.γ) with hMT
  have hMT0 : 0 < MT := by
    have hy : 0 < P.v (i P.T) * s P.T / P.γ :=
      div_pos (mul_pos hvT (hspos _ hTI)) hP.γ_pos
    have hlb : P.v (i P.T) * s P.T / P.γ * P.bl ≤ MT := by
      rw [hMT]; unfold Params.M
      apply le_csInf ((nonempty_Icc.2 hP.bl_lt_bbar.le).image _)
      rintro _ ⟨b, hb, rfl⟩
      have hc : 0 ≤ P.c b := by
        rcases hb.2.lt_or_eq with h | h
        · exact (hP.c_pos b ⟨hb.1, h⟩).le
        · rw [h, hP.c_bbar]
      nlinarith [hb.1]
    have := mul_pos hy hP.bl_pos
    linarith
  set η : ℝ → ℝ := fun t => lam2 t - lam1 t with hηdef
  have hηc : ContinuousOn η (Icc 0 P.T) := hc2.sub hc1
  have hηT : 0 < η P.T := by
    simp only [hηdef]; rw [h1T, h2T, sub_zero]
    exact div_pos hvT (mul_pos hP.γ_pos (hipos _ hTI))
  -- integrands of (11)
  set f1 : ℝ → ℝ := fun r => (lam1 r - lam2 r) * β r * i r with hf1
  set f2 : ℝ → ℝ := fun r => (lam1 r - lam2 r) * β r * s r + P.γ * lam2 r - deriv P.v (i r)
    with hf2
  have hf1I : IntervalIntegrable f1 volume 0 P.T := by
    have : f1 = fun r => β r * ((lam1 r - lam2 r) * i r) := by funext r; simp only [hf1]; ring
    rw [this]
    exact hβI.mul_continuousOn (by rw [huIcc]; exact (hc1.sub hc2).mul hi)
  have hf2I : IntervalIntegrable f2 volume 0 P.T := by
    have : f2 = fun r => β r * ((lam1 r - lam2 r) * s r) + (P.γ * lam2 r - deriv P.v (i r)) := by
      funext r; simp only [hf2]; ring
    rw [this]
    refine IntervalIntegrable.add ?_ ?_
    · exact hβI.mul_continuousOn (by rw [huIcc]; exact (hc1.sub hc2).mul hs)
    · apply ContinuousOn.intervalIntegrable
      rw [huIcc]
      exact (continuousOn_const.mul hc2).sub (hdv.comp_continuousOn hi)
  have hsubI : ∀ a ∈ Icc 0 P.T, ∀ b ∈ Icc 0 P.T, uIcc a b ⊆ uIcc 0 P.T := by
    intro a ha b hb
    apply uIcc_subset_uIcc <;> rw [huIcc] <;> assumption
  have hdiff : ∀ a ∈ Icc 0 P.T, ∀ b ∈ Icc 0 P.T,
      η b - η a = ∫ r in a..b, (f2 r - f1 r) := by
    intro a ha b hb
    have e1a := he1 a ha
    have e1b := he1 b hb
    have e2a := he2 a ha
    have e2b := he2 b hb
    have s1 := intervalIntegral.integral_add_adjacent_intervals (hf1I.mono_set (hsubI a ha b hb))
      (hf1I.mono_set (hsubI b hb P.T hTI))
    have s2 := intervalIntegral.integral_add_adjacent_intervals (hf2I.mono_set (hsubI a ha b hb))
      (hf2I.mono_set (hsubI b hb P.T hTI))
    rw [intervalIntegral.integral_sub (hf2I.mono_set (hsubI a ha b hb))
      (hf1I.mono_set (hsubI a ha b hb))]
    simp only [hηdef]
    linarith
  -- pointwise identity where (12) holds
  have hident : ∀ r ∈ Icc 0 P.T, P.ArgminAt ((lam2 r - lam1 r) * i r * s r) (β r) →
      i r * (f2 r - f1 r) =
        η r * β r * i r ^ 2 - deriv P.v (i r) * i r + P.v (i r) + P.c (β r) - MT := by
    intro r hr harg
    have h13r := h13 r hr
    rw [EpiAuxL12.M_eq harg] at h13r
    simp only [hf1, hf2, hηdef]
    linear_combination (-1 : ℝ) * h13r
  -- main argument
  intro t0 ht0
  by_contra hneg
  push Not at hneg
  have ht0I : t0 ∈ Icc 0 P.T := ⟨ht0.1, ht0.2.le⟩
  set Z := Icc t0 P.T ∩ η ⁻¹' Iic 0 with hZ
  have hZsub : Icc t0 P.T ⊆ Icc 0 P.T := Icc_subset_Icc ht0.1 le_rfl
  have hZc : IsClosed Z := (hηc.mono hZsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := ⟨t0, ⟨le_rfl, ht0.2.le⟩, hneg⟩
  have hZbdd : BddAbove Z := ⟨P.T, fun u hu => hu.1.2⟩
  set τ := sSup Z with hτ
  have hτZ : τ ∈ Z := hZc.csSup_mem hZne hZbdd
  have hτI : τ ∈ Icc 0 P.T := hZsub hτZ.1
  have hητ : η τ ≤ 0 := hτZ.2
  have hτT : τ < P.T := by
    rcases hτZ.1.2.lt_or_eq with h | h
    · exact h
    · exfalso; have := hτZ.2; rw [h] at this; simp only [mem_preimage, mem_Iic] at this
      linarith
  have hpos_after : ∀ u ∈ Icc 0 P.T, τ < u → 0 < η u := by
    intro u hu hτu
    by_contra h
    push Not at h
    have : u ∈ Z := ⟨⟨le_trans hτZ.1.1 hτu.le, hu.2⟩, h⟩
    have := le_csSup hZbdd this
    linarith
  have evIff : ∀ {S : Set ℝ} {a : ℝ} {p : ℝ → Prop}, (∀ᶠ x in 𝓝[S] a, p x) →
      ∃ ε > 0, ∀ ⦃x⦄, dist x a < ε → x ∈ S → p x := by
    intro S a p h
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 h
    exact ⟨ε, hε, fun x hx hxS => hsub ⟨Metric.mem_ball.2 hx, hxS⟩⟩
  -- choose b1 with c small on [b1, bbar]
  have hcw : ContinuousWithinAt P.c (Icc P.bl P.bbar) P.bbar :=
    hP.c_cont P.bbar ⟨hP.bl_lt_bbar.le, le_rfl⟩
  have hcev : ∀ᶠ b in 𝓝[Icc P.bl P.bbar] P.bbar, P.c b < MT / 4 := by
    apply hcw.eventually (Iio_mem_nhds _)
    rw [hP.c_bbar]; linarith
  obtain ⟨εc, hεc, hcε⟩ := evIff hcev
  set b1 := max P.bl (P.bbar - εc / 2) with hb1def
  have hb1 : b1 ∈ Ico P.bl P.bbar := ⟨le_max_left _ _, max_lt hP.bl_lt_bbar (by linarith)⟩
  have hcb1 : ∀ b ∈ Icc b1 P.bbar, P.c b < MT / 4 := by
    intro b hb
    apply hcε _ ⟨le_trans (le_max_left _ _) hb.1, hb.2⟩
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hb.2])]
    have := le_max_right P.bl (P.bbar - εc / 2)
    linarith [hb.1]
  -- continuity at τ
  set y : ℝ → ℝ := fun t => (lam2 t - lam1 t) * i t * s t with hydef
  have hycont : ContinuousOn y (Icc 0 P.T) := ((hc2.sub hc1).mul hi).mul hs
  have hyτ : y τ ≤ 0 := by
    simp only [hydef]
    have := mul_pos (hipos τ hτI) (hspos τ hτI)
    have h' : lam2 τ - lam1 τ ≤ 0 := hητ
    nlinarith
  have hK : 0 < P.c b1 / (P.bbar - P.bl) := div_pos (hP.c_pos b1 hb1) (sub_pos.2 hP.bl_lt_bbar)
  have hev1 : ∀ᶠ r in 𝓝[Icc 0 P.T] τ, y r < P.c b1 / (P.bbar - P.bl) :=
    (hycont τ hτI).eventually (Iio_mem_nhds (lt_of_le_of_lt hyτ hK))
  have hev2 : ∀ᶠ r in 𝓝[Icc 0 P.T] τ, η r < MT / (4 * P.bbar) :=
    (hηc τ hτI).eventually (Iio_mem_nhds (lt_of_le_of_lt hητ (by positivity)))
  obtain ⟨δ, hδ, hδP⟩ := evIff (hev1.and hev2)
  set u := min (τ + δ / 2) P.T with hu
  have hτu : τ < u := lt_min (by linarith) hτT
  have huI : u ∈ Icc 0 P.T := ⟨le_trans hτI.1 hτu.le, min_le_right _ _⟩
  have hηu := hpos_after u huI hτu
  -- the integrand is ≤ -MT/2 a.e. on [τ, u]
  have hbound : ∀ᵐ r ∂(volume.restrict (Icc τ u)), f2 r - f1 r ≤ -(MT / 2) := by
    have h1 := (ae_restrict_iff' measurableSet_Icc).1 hargmin
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1] with r hr hrI
    have hrI' : r ∈ Icc 0 P.T := ⟨le_trans hτI.1 hrI.1, le_trans hrI.2 huI.2⟩
    have hdist : dist r τ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hrI.1])]
      have := min_le_left (τ + δ / 2) P.T
      linarith [hrI.2]
    obtain ⟨hyr, hηr⟩ := hδP hdist hrI'
    have harg := hr hrI'
    have hβr : b1 ≤ β r := EpiAuxL12.argmin_ge hP hb1 hyr harg
    have hcr : P.c (β r) < MT / 4 := hcb1 _ ⟨hβr, harg.1.2⟩
    have hid := hident r hrI' harg
    have hir := hipos r hrI'
    have hir1 := hi1 r hrI'
    have htanr := htan (i r) ⟨hir, hir1⟩
    have hβ0 : 0 ≤ β r := le_trans hP.bl_pos.le harg.1.1
    have hβ1 : β r ≤ P.bbar := harg.1.2
    have hMT4 : 0 < MT / 4 := by linarith
    have hi2 : i r ^ 2 ≤ 1 := pow_le_one₀ hir.le hir1
    have hβi : β r * i r ^ 2 ≤ P.bbar :=
      (mul_le_of_le_one_right hβ0 hi2).trans hβ1
    have hβi0 : 0 ≤ β r * i r ^ 2 := mul_nonneg hβ0 (sq_nonneg _)
    have hfirst : η r * β r * i r ^ 2 ≤ MT / 4 := by
      rw [mul_assoc]
      rcases le_or_gt (η r) 0 with h | h
      · have := mul_nonpos_of_nonpos_of_nonneg h hβi0
        linarith
      · have hηb : η r * (4 * P.bbar) < MT := (lt_div_iff₀ (by positivity)).1 hηr
        have := mul_le_mul_of_nonneg_left hβi h.le
        linarith
    have hnum : i r * (f2 r - f1 r) ≤ -(MT / 2) := by rw [hid]; linarith
    have hFneg : f2 r - f1 r < 0 := neg_of_mul_neg_right (by linarith) hir.le
    have : (1 - i r) * (f2 r - f1 r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hFneg.le
    linarith
  have hint := intervalIntegral.integral_mono_ae_restrict hτu.le
    ((hf2I.sub hf1I).mono_set (hsubI τ hτI u huI)) intervalIntegrable_const hbound
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hd := hdiff τ hτI u huI
  have : (u - τ) * -(MT / 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith
