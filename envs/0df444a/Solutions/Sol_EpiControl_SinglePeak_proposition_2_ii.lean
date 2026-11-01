-- Prove2me | solution 1 for EpiControl.SinglePeak.proposition_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:25:50.431236+00:00
-- url     : https://prove2.me/submissions/fb0f6a74-628b-4689-8fca-5ab03a2dee62

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model
import Theorems.Thm_EpiControl_SinglePeak_proposition_2_i
import Theorems.Thm_EpiControl_SinglePeak_eq_33

open MeasureTheory Set Filter Topology

namespace EpiAuxP2ii

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


theorem evIff {S : Set ℝ} {a : ℝ} {p : ℝ → Prop} (h : ∀ᶠ x in 𝓝[S] a, p x) :
    ∃ ε > 0, ∀ ⦃x⦄, dist x a < ε → x ∈ S → p x := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 h
  exact ⟨ε, hε, fun x hx hxS => hsub ⟨Metric.mem_ball.2 hx, hxS⟩⟩

/-- Sign lemma: if `G' ≤ Ā|G| - δ₀` a.e., then once `G ≤ 0` it stays `< 0`. -/
theorem sign_lemma {T Ab δ0 : ℝ} {G : ℝ → ℝ} (hδ : 0 < δ0) (hA : 0 ≤ Ab)
    (hc : ContinuousOn G (Icc 0 T)) (hac : AbsolutelyContinuousOnInterval G 0 T)
    (hb : ∀ᵐ t, t ∈ Icc 0 T → deriv G t ≤ Ab * |G t| - δ0) :
    ∀ t1 ∈ Icc 0 T, G t1 ≤ 0 → ∀ t ∈ Icc 0 T, t1 < t → G t < 0 := by
  -- local decrease where |G| is small
  have L : ∀ a ∈ Icc 0 T, ∀ b ∈ Icc 0 T, a ≤ b → (∀ r ∈ Icc a b, Ab * |G r| ≤ δ0 / 2) →
      G b - G a ≤ -(δ0 / 2) * (b - a) := by
    intro a ha b hb' hab hsmall
    have hsub : uIcc a b ⊆ uIcc 0 T := by
      apply uIcc_subset_uIcc <;> rw [uIcc_of_le (ha.1.trans ha.2)] <;> assumption
    have hac' := hac.mono hsub
    rw [← hac'.integral_deriv_eq_sub]
    have := intervalIntegral.integral_mono_ae_restrict hab hac'.intervalIntegrable_deriv
      (intervalIntegrable_const (c := -(δ0 / 2))) (by
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        filter_upwards [hb] with r hr hrI
        have hrI' : r ∈ Icc 0 T := ⟨ha.1.trans hrI.1, hrI.2.trans hb'.2⟩
        have := hr hrI'
        have := hsmall r hrI
        linarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  -- near a zero, |G| is small
  have small : ∀ t0 ∈ Icc 0 T, G t0 = 0 → ∃ ρ > 0, ∀ r ∈ Icc 0 T, dist r t0 < ρ →
      Ab * |G r| ≤ δ0 / 2 := by
    intro t0 ht0 hz
    have hcont : ContinuousWithinAt (fun r => Ab * |G r|) (Icc 0 T) t0 :=
      continuousWithinAt_const.mul (hc t0 ht0).abs
    have hev : ∀ᶠ r in 𝓝[Icc 0 T] t0, Ab * |G r| < δ0 / 2 := by
      apply hcont.eventually (Iio_mem_nhds _)
      simp only [hz, abs_zero, mul_zero]; linarith
    obtain ⟨ρ, hρ, h⟩ := evIff hev
    exact ⟨ρ, hρ, fun r hr hd => (h hd hr).le⟩
  -- step a
  have stepA : ∀ t1 ∈ Icc 0 T, G t1 ≤ 0 → ∃ ε > 0, ∀ r ∈ Icc 0 T, t1 < r → r < t1 + ε →
      G r < 0 := by
    intro t1 ht1 hG
    rcases hG.lt_or_eq with hlt | heq
    · have hev : ∀ᶠ r in 𝓝[Icc 0 T] t1, G r < 0 := (hc t1 ht1).eventually (Iio_mem_nhds hlt)
      obtain ⟨ρ, hρ, h⟩ := evIff hev
      refine ⟨ρ, hρ, fun r hr h1 h2 => h ?_ hr⟩
      rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    · obtain ⟨ρ, hρ, h⟩ := small t1 ht1 heq
      refine ⟨ρ, hρ, fun r hr h1 h2 => ?_⟩
      have := L t1 ht1 r hr h1.le (fun q hq => h q ⟨ht1.1.trans hq.1, hq.2.trans hr.2⟩ (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hq.1])]; linarith [hq.2]))
      have : -(δ0 / 2) * (r - t1) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
      linarith
  intro t1 ht1 hG t ht htt
  by_contra hpos
  push Not at hpos
  obtain ⟨ε, hε, hεP⟩ := stepA t1 ht1 hG
  set e := min (ε / 2) ((t - t1) / 2) with he
  have he0 : 0 < e := lt_min (by linarith) (by linarith)
  have het : t1 + e < t := by have := min_le_right (ε / 2) ((t - t1) / 2); linarith
  have heε : e < ε := by have := min_le_left (ε / 2) ((t - t1) / 2); linarith
  set Z := Icc (t1 + e) t ∩ G ⁻¹' Ici 0 with hZ
  have hZsub : Icc (t1 + e) t ⊆ Icc 0 T := Icc_subset_Icc (by linarith [ht1.1]) ht.2
  have hZc : IsClosed Z := (hc.mono hZsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hZne : Z.Nonempty := ⟨t, ⟨het.le, le_rfl⟩, hpos⟩
  have hZbdd : BddBelow Z := ⟨t1 + e, fun r hr => hr.1.1⟩
  set σ := sInf Z with hσ
  have hσZ : σ ∈ Z := hZc.csInf_mem hZne hZbdd
  have hσI : σ ∈ Icc 0 T := hZsub hσZ.1
  have hσ1 : t1 < σ := by linarith [hσZ.1.1]
  have hneg : ∀ r ∈ Icc 0 T, t1 < r → r < σ → G r < 0 := by
    intro r hr h1 h2
    by_cases hre : r < t1 + ε
    · exact hεP r hr h1 hre
    · by_contra hc'
      push Not at hc'
      have : r ∈ Z := ⟨⟨by linarith, by linarith [hσZ.1.2]⟩, hc'⟩
      have := csInf_le hZbdd this
      linarith
  -- a point just left of σ
  have pick : ∀ ρ > 0, ∃ a ∈ Icc 0 T, t1 < a ∧ a < σ ∧ σ - a < ρ := by
    intro ρ hρ
    refine ⟨max (σ - ρ / 2) ((t1 + σ) / 2), ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact le_trans (by linarith [ht1.1]) (le_max_right _ _)
    · exact max_le (by linarith [hσI.2]) (by linarith [hσI.2, ht1.2])
    · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact max_lt (by linarith) (by linarith)
    · have := le_max_left (σ - ρ / 2) ((t1 + σ) / 2); linarith
  rcases (show (0:ℝ) ≤ G σ from hσZ.2).lt_or_eq with hgt | heq
  · have hev : ∀ᶠ r in 𝓝[Icc 0 T] σ, 0 < G r := (hc σ hσI).eventually (Ioi_mem_nhds hgt)
    obtain ⟨ρ, hρ, h⟩ := evIff hev
    obtain ⟨a, haI, ha1, ha2, ha3⟩ := pick ρ hρ
    have := h (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith) haI
    have := hneg a haI ha1 ha2
    linarith
  · obtain ⟨ρ, hρ, h⟩ := small σ hσI heq.symm
    obtain ⟨a, haI, ha1, ha2, ha3⟩ := pick ρ hρ
    have hL := L a haI σ hσI ha2.le (fun q hq => h q ⟨haI.1.trans hq.1, hq.2.trans hσI.2⟩ (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hq.2])]; linarith [hq.1]))
    have := hneg a haI ha1 ha2
    have : -(δ0 / 2) * (σ - a) < 0 := mul_neg_of_neg_of_pos (by linarith) (by linarith)
    linarith


/-- Lipschitz bound from an integral representation. -/
theorem lip_of_integral {T x0 C : ℝ} (hT : 0 ≤ T) {f F : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 T) (hb : ∀ r ∈ Icc 0 T, |f r| ≤ C)
    (hF : ∀ t ∈ Icc 0 T, F t = x0 + ∫ r in (0:ℝ)..t, f r) :
    LipschitzOnWith (Real.toNNReal C) F (Icc 0 T) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0 ⟨le_rfl, hT⟩)
  have huIcc : uIcc 0 T = Icc 0 T := uIcc_of_le hT
  have hkI : ∀ t ∈ Icc 0 T, IntervalIntegrable f volume 0 t := fun t ht =>
    hf.mono_set (by rw [huIcc, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hC, hF t ht, hF u hu]
  have : x0 + (∫ r in (0:ℝ)..t, f r) - (x0 + ∫ r in (0:ℝ)..u, f r) = ∫ r in u..t, f r := by
    rw [← intervalIntegral.integral_interval_sub_left (hkI t ht) (hkI u hu)]; ring
  rw [this, ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro r hr
  rw [Real.norm_eq_abs]
  apply hb
  have := uIoc_subset_uIcc hr
  rw [mem_uIcc] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;>
    linarith [ht.1, ht.2, hu.1, hu.2]

open EpiControl.SinglePeak in
theorem M_le {P : Params} (hP : P.Standing) (y y' : ℝ) :
    P.M y ≤ P.M y' + |y - y'| * P.bbar := by
  have hf : ContinuousOn (fun b => y' * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  obtain ⟨b0, hb0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 hP.bl_lt_bbar.le) hf
  have hM' : P.M y' = y' * b0 + P.c b0 := by
    unfold Params.M
    apply IsLeast.csInf_eq
    refine ⟨⟨b0, hb0, rfl⟩, ?_⟩
    rintro _ ⟨b', hb', rfl⟩
    exact hmin hb'
  have hf2 : ContinuousOn (fun b => y * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  have hbdd : BddBelow ((fun b => y * b + P.c b) '' Icc P.bl P.bbar) :=
    (isCompact_Icc.image_of_continuousOn hf2).bddBelow
  have h1 : P.M y ≤ y * b0 + P.c b0 := csInf_le hbdd ⟨b0, hb0, rfl⟩
  have hb0' : 0 ≤ b0 := le_trans hP.bl_pos.le hb0.1
  have h2 : (y - y') * b0 ≤ |y - y'| * P.bbar :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hb0').trans
      (mul_le_mul_of_nonneg_left hb0.2 (abs_nonneg _))
  rw [hM']
  nlinarith

open EpiControl.SinglePeak in
theorem M_lip {P : Params} (hP : P.Standing) : LipschitzWith (Real.toNNReal P.bbar) P.M := by
  have hbb : 0 ≤ P.bbar := (hP.bl_pos.trans hP.bl_lt_bbar).le
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hbb, abs_le]
  have h1 := M_le hP y y'
  have h2 := M_le hP y' y
  rw [abs_sub_comm] at h2
  constructor <;> nlinarith

end EpiAuxP2ii


open EpiControl.SinglePeak in
theorem EpiAuxP2ii.M_eq {P : Params} {y b : ℝ} (h : P.ArgminAt y b) :
    P.M y = y * b + P.c b := by
  unfold Params.M
  apply IsLeast.csInf_eq
  refine ⟨⟨b, h.1, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩
  exact h.2 b' hb'


open EpiControl.SinglePeak in
theorem EpiAuxP2ii.M_strict {P : Params} (hP : P.Standing) {y y' : ℝ} (h : y' ≤ y) :
    P.M y' + (y - y') * P.bl ≤ P.M y := by
  have hf : ContinuousOn (fun b => y * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  obtain ⟨b0, hb0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 hP.bl_lt_bbar.le) hf
  have hM : P.M y = y * b0 + P.c b0 :=
    EpiAuxP2ii.M_eq ⟨hb0, fun b' hb' => hmin hb'⟩
  have hf2 : ContinuousOn (fun b => y' * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  have hbdd : BddBelow ((fun b => y' * b + P.c b) '' Icc P.bl P.bbar) :=
    (isCompact_Icc.image_of_continuousOn hf2).bddBelow
  have h1 : P.M y' ≤ y' * b0 + P.c b0 := csInf_le hbdd ⟨b0, hb0, rfl⟩
  have : (y - y') * P.bl ≤ (y - y') * b0 := mul_le_mul_of_nonneg_left hb0.1 (by linarith)
  rw [hM]; nlinarith

/-- Negative derivative within a set gives a sign of the increments nearby. -/
theorem EpiAuxP2ii.incr_of_deriv_neg {f : ℝ → ℝ} {f' x : ℝ} {S : Set ℝ}
    (hf : HasDerivWithinAt f f' S x) (hneg : f' < 0) :
    ∃ ρ > 0, ∀ u ∈ S, dist u x < ρ → (x < u → f u < f x) ∧ (u < x → f x < f u) := by
  have ht := hasDerivWithinAt_iff_tendsto_slope.1 hf
  have hev : ∀ᶠ u in 𝓝[S \ {x}] x, slope f x u < 0 := ht.eventually (Iio_mem_nhds hneg)
  obtain ⟨ρ, hρ, h⟩ := EpiAuxP2ii.evIff hev
  refine ⟨ρ, hρ, fun u hu hd => ⟨fun hxu => ?_, fun hux => ?_⟩⟩
  · have := h hd ⟨hu, by simp only [mem_singleton_iff]; exact hxu.ne'⟩
    rw [slope_def_field, div_neg_iff] at this
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · have := h hd ⟨hu, by simp only [mem_singleton_iff]; exact hux.ne⟩
    rw [slope_def_field, div_neg_iff] at this
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    ∀ t ∈ Ico 0 P.T,
      0 < gain η s i P.T ∧ gain η s i P.T < gain η s i t ∧
      gain η s i t <
        1 / P.γ * (P.v 1 + deriv P.v 1 * (Real.exp ((P.T - t) * P.γ) - 1)) := by
  obtain ⟨hgd, hgTv⟩ := proposition_2_i P hP β s i hopt η hη
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hTI : P.T ∈ Icc 0 P.T := ⟨hT, le_rfl⟩
  obtain ⟨_, hiexp, hsexp⟩ := EpiAuxP2ii.path_exp hP hopt.1 hopt.2.1
  have hipos : ∀ r ∈ Icc 0 P.T, 0 < i r := fun r hr => by
    rw [hiexp r hr]; exact mul_pos hP.i0_mem.1 (Real.exp_pos _)
  have hspos : ∀ r ∈ Icc 0 P.T, 0 < s r := fun r hr => by
    rw [hsexp r hr]; exact mul_pos hP.s0_mem.1 (Real.exp_pos _)
  have his1 : ∀ r ∈ Icc 0 P.T, i r + s r ≤ 1 := by
    intro r hr
    have h := ((eq_33 P hP).2 β s i hopt r hr).1
    have hs2 : 0 < s r ^ 2 := by have := hspos r hr; positivity
    have := le_of_mul_le_mul_left h hs2
    linarith
  have hi1 : ∀ r ∈ Icc 0 P.T, i r ≤ 1 := fun r hr => by linarith [his1 r hr, hspos r hr]
  have hs1 : ∀ r ∈ Icc 0 P.T, s r ≤ 1 := fun r hr => by linarith [his1 r hr, hipos r hr]
  set g := gain η s i with hgdef
  have hgpos : ∀ r ∈ Icc 0 P.T, 0 < g r := fun r hr =>
    mul_pos (mul_pos (hη.2.2.2.2 r hr) (hipos r hr)) (hspos r hr)
  -- convexity facts on v
  have hvdiff : Differentiable ℝ P.v := hP.v_C1.differentiable one_ne_zero
  set Q : ℝ → ℝ := fun x => deriv P.v x * x - P.v x with hQ
  have hQ0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ Q x := by
    intro x hx
    rcases hx.1.lt_or_eq with h | h
    · have := hP.v_convex.slope_le_deriv (x := 0) (y := x) ⟨le_rfl, zero_le_one⟩ hx h
        (hvdiff x)
      rw [slope_def_field, hP.v_zero, sub_zero, sub_zero, div_le_iff₀ h] at this
      simp only [hQ]; linarith
    · simp only [hQ, ← h, hP.v_zero]; ring_nf; rfl
  have hQmono : ∀ x ∈ Icc (0:ℝ) 1, Q x ≤ Q 1 := by
    intro x hx
    rcases hx.2.lt_or_eq with h | h
    · have h1 := hP.v_convex.slope_le_deriv hx ⟨zero_le_one, le_rfl⟩ h (hvdiff 1)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h1
      have h2 := hP.v_convex.monotoneOn_deriv (fun y _ => hvdiff y) hx
        ⟨zero_le_one, le_rfl⟩ h.le
      simp only [hQ]
      nlinarith [hx.1]
    · rw [h]
  -- positivity of g T
  have hvT : 0 < P.v (i P.T) := by
    rw [← hP.v_zero]
    exact hP.v_strictMono ⟨le_rfl, zero_le_one⟩ ⟨(hipos _ hTI).le, hi1 _ hTI⟩ (hipos _ hTI)
  have hgT0 : 0 < g P.T := hgpos P.T hTI
  -- G1 negative where g ≤ g T
  set G1 : ℝ → ℝ := fun t => -P.γ * g t + s t * (P.M (g t) - P.M (g P.T) -
      (deriv P.v (i t) * i t - P.v (i t))) with hG1
  have hG1neg : ∀ u ∈ Icc 0 P.T, g u ≤ g P.T → G1 u < 0 := by
    intro u hu hle
    have hM : P.M (g u) ≤ P.M (g P.T) := by
      have := EpiAuxP2ii.M_strict hP hle
      nlinarith [hP.bl_pos]
    have hQu := hQ0 (i u) ⟨(hipos u hu).le, hi1 u hu⟩
    simp only [hQ] at hQu
    have : s u * (P.M (g u) - P.M (g P.T) - (deriv P.v (i u) * i u - P.v (i u))) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hspos u hu).le (by linarith)
    have := mul_pos hP.γ_pos (hgpos u hu)
    simp only [hG1]; linarith
  -- part A: g t > g T for t < T
  have partA : ∀ t ∈ Ico 0 P.T, g P.T < g t := by
    intro t ht
    by_contra hc
    push Not at hc
    have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
    obtain ⟨ε, hε, hεP⟩ := EpiAuxP2ii.incr_of_deriv_neg (hgd P.T hTI)
      (hG1neg P.T hTI le_rfl)
    -- points in (T - ε, T) have g > g T
    have hnear : ∀ u ∈ Icc 0 P.T, P.T - ε < u → u < P.T → g P.T < g u := by
      intro u hu h1 h2
      exact (hεP u hu (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)).2 h2
    by_cases hte : P.T - ε / 2 < t
    · exact absurd (hnear t htI (by linarith) ht.2) (not_lt.2 hc)
    push Not at hte
    set Z := Icc t (P.T - ε / 2) ∩ g ⁻¹' Iic (g P.T) with hZ
    have hZsub : Icc t (P.T - ε / 2) ⊆ Icc 0 P.T := Icc_subset_Icc ht.1 (by linarith)
    have hgc : ContinuousOn g (Icc 0 P.T) := fun r hr => (hgd r hr).continuousWithinAt
    have hZc : IsClosed Z :=
      (hgc.mono hZsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hZne : Z.Nonempty := ⟨t, ⟨le_rfl, hte⟩, hc⟩
    have hZbdd : BddAbove Z := ⟨P.T - ε / 2, fun r hr => hr.1.2⟩
    set σ := sSup Z with hσ
    have hσZ : σ ∈ Z := hZc.csSup_mem hZne hZbdd
    have hσI : σ ∈ Icc 0 P.T := hZsub hσZ.1
    obtain ⟨δ, hδ, hδP⟩ := EpiAuxP2ii.incr_of_deriv_neg (hgd σ hσI) (hG1neg σ hσI hσZ.2)
    set u := min (σ + δ / 2) (P.T - ε / 4) with hu
    have hσu : σ < u := lt_min (by linarith) (by linarith [hσZ.1.2])
    have huT : u < P.T := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have huI : u ∈ Icc 0 P.T := ⟨le_trans hσI.1 hσu.le, huT.le⟩
    have hu1 : u ≤ σ + δ / 2 := min_le_left _ _
    have hgu : g u < g σ := (hδP u huI (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith)).1 hσu
    by_cases hue : u ≤ P.T - ε / 2
    · have htσ : t ≤ σ := hσZ.1.1
      have hgσ : g σ ≤ g P.T := hσZ.2
      have htu : t ≤ u := by linarith
      have hguT : g u ≤ g P.T := by linarith
      have : u ∈ Z := ⟨⟨htu, hue⟩, hguT⟩
      have := le_csSup hZbdd this
      linarith
    · push Not at hue
      have := hnear u huI (by linarith) huT
      have : g σ ≤ g P.T := hσZ.2
      linarith
  intro t ht
  refine ⟨hgT0, partA t ht, ?_⟩
  -- part B: Gronwall-type upper bound
  have htI : t ∈ Icc 0 P.T := ⟨ht.1, ht.2.le⟩
  set Q1 := Q 1 with hQ1
  set ψ : ℝ → ℝ := fun u => Real.exp (P.γ * u) * (g u + Q1 / P.γ) with hψ
  have hgc : ContinuousOn g (Icc 0 P.T) := fun r hr => (hgd r hr).continuousWithinAt
  have hψmono : StrictMonoOn ψ (Icc t P.T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc t P.T)
    · apply ContinuousOn.mul (Continuous.continuousOn (by fun_prop))
      exact (hgc.mono (Icc_subset_Icc ht.1 le_rfl)).add continuousOn_const
    · intro x hx
      rw [interior_Icc] at hx
      have hxI : x ∈ Icc 0 P.T := ⟨by linarith [ht.1, hx.1], hx.2.le⟩
      have hgx : HasDerivAt g (G1 x) x :=
        (hgd x hxI).hasDerivAt (Icc_mem_nhds (by linarith [ht.1, hx.1]) hx.2)
      have hE : HasDerivAt (fun u => Real.exp (P.γ * u)) (Real.exp (P.γ * x) * (P.γ * 1)) x :=
        ((hasDerivAt_id x).const_mul P.γ).exp
      have hd := hE.mul (hgx.add_const (Q1 / P.γ))
      rw [show deriv ψ x = _ from hd.deriv]
      have hMs := EpiAuxP2ii.M_strict hP (partA x ⟨hxI.1, hx.2⟩).le
      have hgx' := partA x ⟨hxI.1, hx.2⟩
      have hQi := hQmono (i x) ⟨(hipos x hxI).le, hi1 x hxI⟩
      have hQi0 := hQ0 (i x) ⟨(hipos x hxI).le, hi1 x hxI⟩
      have hsx := hspos x hxI
      have hsx1 := hs1 x hxI
      have key : 0 < P.γ * (g x + Q1 / P.γ) + G1 x := by
        simp only [hG1]
        have e : P.γ * (g x + Q1 / P.γ) = P.γ * g x + Q1 := by
          rw [mul_add, mul_div_cancel₀ _ hP.γ_pos.ne']
        rw [e]
        have hpos1 : 0 < s x * (P.M (g x) - P.M (g P.T)) := by
          apply mul_pos hsx
          have := mul_pos (sub_pos.2 hgx') hP.bl_pos
          linarith
        have hpos2 : s x * Q (i x) ≤ Q1 := by
          have : s x * Q (i x) ≤ 1 * Q (i x) := mul_le_mul_of_nonneg_right hsx1 hQi0
          linarith
        simp only [hQ] at hpos2
        nlinarith
      have := Real.exp_pos (P.γ * x)
      have : Real.exp (P.γ * x) * (P.γ * 1) * (g x + Q1 / P.γ) +
          Real.exp (P.γ * x) * G1 x = Real.exp (P.γ * x) * (P.γ * (g x + Q1 / P.γ) + G1 x) := by
        ring
      rw [this]
      positivity
  have hlt := hψmono ⟨le_rfl, ht.2.le⟩ ⟨ht.2.le, le_rfl⟩ ht.2
  simp only [hψ] at hlt
  -- g T ≤ v 1 / γ
  have hgTle : g P.T ≤ P.v 1 / P.γ := by
    rw [hgTv]
    have hv1 : P.v (i P.T) ≤ P.v 1 :=
      hP.v_strictMono.monotoneOn ⟨(hipos _ hTI).le, hi1 _ hTI⟩ ⟨zero_le_one, le_rfl⟩
        (hi1 _ hTI)
    have : P.v (i P.T) * s P.T ≤ P.v 1 := by
      have := mul_le_mul hv1 (hs1 _ hTI) (hspos _ hTI).le (by linarith)
      linarith
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right this hP.γ_pos.le
  have hexp : Real.exp ((P.T - t) * P.γ) * Real.exp (P.γ * t) = Real.exp (P.γ * P.T) := by
    rw [← Real.exp_add]; ring_nf
  have hQ1def : Q1 = deriv P.v 1 - P.v 1 := by simp only [hQ1, hQ]; ring
  have hEt := Real.exp_pos (P.γ * t)
  have hET := Real.exp_pos ((P.T - t) * P.γ)
  -- from hlt: g t + Q1/γ < e^{(T-t)γ} (g T + Q1/γ)
  have h1 : g t + Q1 / P.γ < Real.exp ((P.T - t) * P.γ) * (g P.T + Q1 / P.γ) := by
    rw [← hexp] at hlt
    have : Real.exp (P.γ * t) * (g t + Q1 / P.γ) <
        Real.exp (P.γ * t) * (Real.exp ((P.T - t) * P.γ) * (g P.T + Q1 / P.γ)) := by
      linarith
    exact lt_of_mul_lt_mul_left this hEt.le
  have h2 : Real.exp ((P.T - t) * P.γ) * (g P.T + Q1 / P.γ) ≤
      Real.exp ((P.T - t) * P.γ) * (P.v 1 / P.γ + Q1 / P.γ) :=
    mul_le_mul_of_nonneg_left (by linarith) hET.le
  have h3 : Real.exp ((P.T - t) * P.γ) * (P.v 1 / P.γ + Q1 / P.γ) - Q1 / P.γ =
      1 / P.γ * (P.v 1 + deriv P.v 1 * (Real.exp ((P.T - t) * P.γ) - 1)) := by
    rw [hQ1def]; field_simp; ring
  show g t < _
  linarith
