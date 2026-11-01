-- Prove2me | solution 1 for EpiControl.SinglePeak.g_strictly_quasiconcave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:19:26.181966+00:00
-- url     : https://prove2.me/submissions/128a0433-4681-47b4-8b06-173cc1e0aaf3

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model
import Theorems.Thm_EpiControl_SinglePeak_proposition_2_i
import Theorems.Thm_EpiControl_SinglePeak_proposition_2_ii
import Theorems.Thm_EpiControl_SinglePeak_eq_37
import Theorems.Thm_EpiControl_SinglePeak_eq_33

open MeasureTheory Set Filter Topology

namespace EpiAuxGQ

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

end EpiAuxGQ

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (dc : ℝ)
    (hA1 : P.Assumption1 dc) (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) (η : ℝ → ℝ)
    (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    ∃ tstar ∈ Icc 0 P.T,
      StrictMonoOn (gain η s i) (Icc 0 tstar) ∧ StrictAntiOn (gain η s i) (Icc tstar P.T) := by
  obtain ⟨hgd, -⟩ := proposition_2_i P hP β s i hopt η hη
  have h2ii := proposition_2_ii P hP β s i hopt η hη
  set g : ℝ → ℝ := gain η s i with hgdef
  set G1 : ℝ → ℝ := fun t =>
    -P.γ * g t + s t * (P.M (g t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t)))
    with hG1def
  have h37 : ∀ᵐ t ∂(volume.restrict (Icc 0 P.T)),
      DifferentiableAt ℝ G1 t ∧
      deriv G1 t ≤
        (-P.γ + β t * (s t - i t) - deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t) * G1 t -
          g t * β t * i t *
            (4 * deriv (deriv P.v) (i t) / (27 * dc) * (P.bbar / P.bl - 1) + P.γ) :=
    eq_37 P hP dc hA1 β s i hopt η hη hconv
  have hT0 : 0 < P.T := hP.T_pos
  have hT : 0 ≤ P.T := hT0.le
  have hTI : P.T ∈ Icc 0 P.T := ⟨hT, le_rfl⟩
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  -- basic bounds
  have hgT : 0 < g P.T := (h2ii 0 ⟨le_rfl, hT0⟩).1
  have hgge : ∀ t ∈ Icc 0 P.T, g P.T ≤ g t := by
    intro t ht
    rcases ht.2.lt_or_eq with h | h
    · exact (h2ii t ⟨ht.1, h⟩).2.1.le
    · rw [h]
  obtain ⟨hβI, hiexp, hsexp⟩ := EpiAuxGQ.path_exp hP hopt.1 hopt.2.1
  have hs := hopt.2.1.1
  have hi := hopt.2.1.2.1
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
  have hβB : ∀ r ∈ Icc 0 P.T, β r ∈ Icc P.bl P.bbar := hopt.1.2
  have hbb : 0 < P.bbar := hP.bl_pos.trans hP.bl_lt_bbar
  -- smoothness of v
  have hv2 : ContDiff ℝ (1 + 1) P.v := hA1.1
  have hdv1 : ContDiff ℝ 1 (deriv P.v) := (contDiff_succ_iff_deriv.1 hv2).2.2
  have hddv : Continuous (deriv (deriv P.v)) := hdv1.continuous_deriv le_rfl
  have hdv_diff : Differentiable ℝ (deriv P.v) := hdv1.differentiable one_ne_zero
  have hdv : Continuous (deriv P.v) := hdv1.continuous
  have hv_diff : Differentiable ℝ P.v := hP.v_C1.differentiable one_ne_zero
  have hvc : Continuous P.v := hP.v_C1.continuous
  obtain ⟨V, hV⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hddv.continuousOn (s := Icc (0:ℝ) 1))
  obtain ⟨V1, hV1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hdv.continuousOn (s := Icc (0:ℝ) 1))
  have hV0 : 0 ≤ V := le_trans (norm_nonneg _) (hV 0 ⟨le_rfl, zero_le_one⟩)
  have hV10 : 0 ≤ V1 := le_trans (norm_nonneg _) (hV1 0 ⟨le_rfl, zero_le_one⟩)
  have himap : MapsTo i (Icc 0 P.T) (Icc 0 1) := fun r hr => ⟨(hipos r hr).le, hi1 r hr⟩
  -- dc ≤ 0
  have hdc : dc ≤ 0 := by
    apply le_of_tendsto hA1.2.1
    filter_upwards [Ioo_mem_nhdsLT hP.bl_lt_bbar] with b hb
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith [hb.2])
    have := hP.c_antitone ⟨hb.1.le, hb.2.le⟩ ⟨hP.bl_lt_bbar.le, le_rfl⟩ hb.2.le
    linarith
  -- the factor K is bounded below
  set kfun : ℝ → ℝ := fun x =>
    4 * deriv (deriv P.v) x / (27 * dc) * (P.bbar / P.bl - 1) + P.γ with hkfun
  have hkpos : ∀ x ∈ Icc (0:ℝ) 1, 0 < kfun x := by
    intro x hx
    have hA := hA1.2.2 x hx
    simp only [hkfun]
    rcases hdc.lt_or_eq with hlt | heq
    · set w := deriv (deriv P.v) x
      set D := -dc with hD
      have hD0 : 0 < D := by linarith
      rw [abs_of_neg hlt, ← hD] at hA
      have hbl := hP.bl_pos
      have hgap : 0 < P.bbar - P.bl := sub_pos.2 hP.bl_lt_bbar
      have hw : w < P.γ * (27 / 4 * (P.bl / (P.bbar - P.bl)) * D) :=
        (div_lt_iff₀' hP.γ_pos).1 hA
      have hw' : 4 * w * (P.bbar - P.bl) < 27 * P.γ * D * P.bl := by
        have := mul_lt_mul_of_pos_right hw (by positivity : 0 < 4 * (P.bbar - P.bl))
        have e : P.γ * (27 / 4 * (P.bl / (P.bbar - P.bl)) * D) * (4 * (P.bbar - P.bl)) =
            27 * P.γ * D * P.bl := by field_simp
        linarith
      have e2 : 4 * w / (27 * dc) * (P.bbar / P.bl - 1) =
          -(4 * w * (P.bbar - P.bl) / (27 * D * P.bl)) := by
        rw [hD]; field_simp
      rw [e2]
      have : 4 * w * (P.bbar - P.bl) / (27 * D * P.bl) < P.γ := by
        rw [div_lt_iff₀ (by positivity)]; linarith
      linarith
    · rw [heq]; simp [hP.γ_pos]
  have hkcont : ContinuousOn kfun (Icc 0 1) := by
    apply Continuous.continuousOn
    exact ((continuous_const.mul hddv).div_const _ |>.mul continuous_const).add continuous_const
  obtain ⟨x0, hx0, hkmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hkcont
  set κ := kfun x0
  have hκ : 0 < κ := hkpos x0 hx0
  -- i bounded below
  obtain ⟨tm, htm, himin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hi
  have himpos : 0 < i tm := hipos tm htm
  -- continuity of g, M, G1
  have hgc : ContinuousOn g (Icc 0 P.T) := fun t ht => (hgd t ht).continuousWithinAt
  have hMl := EpiAuxGQ.M_lip hP
  have hMc : Continuous P.M := hMl.continuous
  have hG1c : ContinuousOn G1 (Icc 0 P.T) := by
    apply ContinuousOn.add (continuousOn_const.mul hgc)
    apply hs.mul
    apply ContinuousOn.sub (ContinuousOn.sub (hMc.comp_continuousOn hgc) continuousOn_const)
    exact ((hdv.comp_continuousOn hi).mul hi).sub (hvc.comp_continuousOn hi)
  obtain ⟨CG, hCG⟩ := isCompact_Icc.exists_bound_of_continuousOn hG1c
  have hCG0 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG 0 ⟨le_rfl, hT⟩)
  -- Lipschitz / absolutely continuous pieces
  have hglip : LipschitzOnWith (Real.toNNReal CG) g (Icc 0 P.T) := by
    apply (convex_Icc 0 P.T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hgd
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hCG0]
    exact hCG x hx
  have hβsiI : IntervalIntegrable (fun r => β r * i r * s r) volume 0 P.T := by
    have : (fun r => β r * i r * s r) = fun r => β r * (i r * s r) := by funext r; ring
    rw [this]; exact hβI.mul_continuousOn (by rw [huIcc]; exact hi.mul hs)
  have hβbound : ∀ r ∈ Icc 0 P.T, |β r| ≤ P.bbar := fun r hr => by
    rw [abs_of_pos (lt_of_lt_of_le hP.bl_pos (hβB r hr).1)]; exact (hβB r hr).2
  have hβis : ∀ r ∈ Icc 0 P.T, |β r * i r * s r| ≤ P.bbar := by
    intro r hr
    rw [abs_mul, abs_mul, abs_of_pos (hipos r hr), abs_of_pos (hspos r hr)]
    have h1 := hβbound r hr
    have h2 : i r * s r ≤ 1 := by
      have := mul_le_mul (hi1 r hr) (hs1 r hr) (hspos r hr).le zero_le_one
      linarith
    have h3 : 0 ≤ i r * s r := (mul_pos (hipos r hr) (hspos r hr)).le
    calc |β r| * i r * s r = |β r| * (i r * s r) := by ring
      _ ≤ P.bbar * 1 := mul_le_mul h1 h2 h3 hbb.le
      _ = P.bbar := mul_one _
  have hslip : LipschitzOnWith (Real.toNNReal P.bbar) s (Icc 0 P.T) := by
    apply EpiAuxGQ.lip_of_integral hT hβsiI.neg (x0 := P.s0)
    · intro r hr; simp only [Pi.neg_apply, abs_neg]; exact hβis r hr
    · intro t ht
      rw [(hopt.2.1.2.2 t ht).1]; simp only [Pi.neg_apply, intervalIntegral.integral_neg]; ring
  have hilip : LipschitzOnWith (Real.toNNReal (P.bbar + P.γ)) i (Icc 0 P.T) := by
    apply EpiAuxGQ.lip_of_integral hT (hβsiI.sub (hi.intervalIntegrable_of_Icc hT |>.const_mul
      P.γ)) (x0 := P.i0)
    · intro r hr
      calc |β r * i r * s r - P.γ * i r| ≤ |β r * i r * s r| + |P.γ * i r| := abs_sub _ _
        _ ≤ P.bbar + P.γ := by
          gcongr
          · exact hβis r hr
          · rw [abs_mul, abs_of_pos hP.γ_pos, abs_of_pos (hipos r hr)]
            exact mul_le_of_le_one_right hP.γ_pos.le (hi1 r hr)
    · intro t ht; exact (hopt.2.1.2.2 t ht).2
  have hdvlip : LipschitzOnWith (Real.toNNReal V) (deriv P.v) (Icc 0 1) := by
    apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hdv_diff x)
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hV0]
    exact hV x hx
  have hvlip : LipschitzOnWith (Real.toNNReal V1) P.v (Icc 0 1) := by
    apply (convex_Icc (0:ℝ) 1).lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hv_diff x)
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hV10]
    exact hV1 x hx
  have AC : ∀ {f : ℝ → ℝ} {K : NNReal}, LipschitzOnWith K f (Icc 0 P.T) →
      AbsolutelyContinuousOnInterval f 0 P.T := by
    intro f K h
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := K)
    rw [huIcc]; exact h
  have hACconst : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun _ => c) 0 P.T := fun c =>
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have hG1ac : AbsolutelyContinuousOnInterval G1 0 P.T := by
    have a1 := AC hglip
    have a2 := AC hslip
    have a3 := AC ((hMl.lipschitzOnWith (s := univ)).comp hglip (mapsTo_univ _ _))
    have a4 := AC (hdvlip.comp hilip himap)
    have a5 := AC hilip
    have a6 := AC (hvlip.comp hilip himap)
    have := ((hACconst (-P.γ)).fun_mul a1).fun_add
      (a2.fun_mul ((a3.fun_sub (hACconst (P.M (g P.T)))).fun_sub ((a4.fun_mul a5).fun_sub a6)))
    exact this
  -- the a.e. differential inequality
  set Ab := P.γ + P.bbar + V / g P.T with hAb
  set δ0 := g P.T * P.bl * i tm * κ with hδ0
  have hδ0pos : 0 < δ0 := by
    have := hP.bl_pos; positivity
  have hAb0 : 0 ≤ Ab := by
    have := hP.γ_pos; have := hgT; positivity
  have hb : ∀ᵐ t, t ∈ Icc 0 P.T → deriv G1 t ≤ Ab * |G1 t| - δ0 := by
    rw [← ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h37, ae_restrict_mem measurableSet_Icc] with t ⟨_, ht37⟩ ht
    have hgt : 0 < g t := lt_of_lt_of_le hgT (hgge t ht)
    have hit := hipos t ht
    have hst := hspos t ht
    have hw : |deriv (deriv P.v) (i t)| ≤ V := hV (i t) (himap ht)
    have e1 : |β t * (s t - i t)| ≤ P.bbar := by
      rw [abs_mul]
      have : |s t - i t| ≤ 1 := abs_sub_le_iff.2 ⟨by linarith [hs1 t ht], by linarith [hi1 t ht]⟩
      calc |β t| * |s t - i t| ≤ P.bbar * 1 :=
            mul_le_mul (hβbound t ht) this (abs_nonneg _) hbb.le
        _ = P.bbar := mul_one _
    have e2 : |deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t| ≤ V / g P.T := by
      rw [abs_div, abs_of_pos hgt]
      have h1 : |deriv (deriv P.v) (i t) * i t ^ 2 * s t| ≤ V := by
        rw [abs_mul, abs_mul, abs_of_pos (pow_pos hit 2), abs_of_pos hst]
        have h2 : i t ^ 2 * s t ≤ 1 := by
          have := pow_le_one₀ hit.le (hi1 t ht) (n := 2)
          have := mul_le_mul this (hs1 t ht) hst.le zero_le_one
          linarith
        calc |deriv (deriv P.v) (i t)| * i t ^ 2 * s t
            = |deriv (deriv P.v) (i t)| * (i t ^ 2 * s t) := by ring
          _ ≤ V * 1 := mul_le_mul hw h2 (by positivity) hV0
          _ = V := mul_one _
      calc |deriv (deriv P.v) (i t) * i t ^ 2 * s t| / g t ≤ V / g t :=
            div_le_div_of_nonneg_right h1 hgt.le
        _ ≤ V / g P.T := div_le_div_of_nonneg_left hV0 hgT (hgge t ht)
    have hAabs : |-P.γ + β t * (s t - i t) - deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t|
        ≤ Ab := by
      have := abs_sub (-P.γ + β t * (s t - i t)) (deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t)
      have := abs_add_le (-P.γ) (β t * (s t - i t))
      rw [abs_neg, abs_of_pos hP.γ_pos] at this
      simp only [hAb]
      linarith
    have hAG : (-P.γ + β t * (s t - i t) - deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t) * G1 t
        ≤ Ab * |G1 t| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hAabs (abs_nonneg _)
    have hK : κ ≤ 4 * deriv (deriv P.v) (i t) / (27 * dc) * (P.bbar / P.bl - 1) + P.γ :=
      hkmin (himap ht)
    have hB : δ0 ≤ g t * β t * i t *
        (4 * deriv (deriv P.v) (i t) / (27 * dc) * (P.bbar / P.bl - 1) + P.γ) := by
      have hβt := hβB t ht
      have hbl := hP.bl_pos
      have m1 : g P.T * P.bl ≤ g t * β t :=
        mul_le_mul (hgge t ht) hβt.1 hbl.le hgt.le
      have m2 : g P.T * P.bl * i tm ≤ g t * β t * i t :=
        mul_le_mul m1 (himin ht) himpos.le (mul_nonneg hgt.le (by linarith [hβt.1]))
      exact mul_le_mul m2 hK hκ.le (mul_nonneg (mul_nonneg hgt.le (by linarith [hβt.1])) hit.le)
    linarith
  have hsign := EpiAuxGQ.sign_lemma hδ0pos hAb0 hG1c hG1ac hb
  have hderiv : ∀ x ∈ Ioo 0 P.T, deriv g x = G1 x := fun x hx =>
    ((hgd x ⟨hx.1.le, hx.2.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hx.2)).deriv
  by_cases hZ : ∃ t ∈ Icc 0 P.T, G1 t ≤ 0
  · set Z := Icc 0 P.T ∩ G1 ⁻¹' Iic 0 with hZdef
    have hZc : IsClosed Z := hG1c.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    obtain ⟨t1, ht1, ht1'⟩ := hZ
    have hZne : Z.Nonempty := ⟨t1, ht1, ht1'⟩
    have hZbdd : BddBelow Z := ⟨0, fun r hr => hr.1.1⟩
    set tstar := sInf Z with htstar
    have htZ : tstar ∈ Z := hZc.csInf_mem hZne hZbdd
    have htI : tstar ∈ Icc 0 P.T := htZ.1
    have hbefore : ∀ t ∈ Icc 0 P.T, t < tstar → 0 < G1 t := by
      intro t ht hlt
      by_contra hc
      push Not at hc
      have := csInf_le hZbdd (⟨ht, hc⟩ : t ∈ Z)
      linarith
    refine ⟨tstar, htI, ?_, ?_⟩
    · apply strictMonoOn_of_deriv_pos (convex_Icc 0 tstar)
        (hgc.mono (Icc_subset_Icc le_rfl htI.2))
      intro x hx
      rw [interior_Icc] at hx
      have hxT : x ∈ Ioo 0 P.T := ⟨hx.1, lt_of_lt_of_le hx.2 htI.2⟩
      rw [hderiv x hxT]
      exact hbefore x ⟨hxT.1.le, hxT.2.le⟩ hx.2
    · apply strictAntiOn_of_deriv_neg (convex_Icc tstar P.T)
        (hgc.mono (Icc_subset_Icc htI.1 le_rfl))
      intro x hx
      rw [interior_Icc] at hx
      have hxT : x ∈ Ioo 0 P.T := ⟨lt_of_le_of_lt htI.1 hx.1, hx.2⟩
      rw [hderiv x hxT]
      exact hsign tstar htI htZ.2 x ⟨hxT.1.le, hxT.2.le⟩ hx.1
  · push Not at hZ
    refine ⟨P.T, hTI, ?_, ?_⟩
    · apply strictMonoOn_of_deriv_pos (convex_Icc 0 P.T) hgc
      intro x hx
      rw [interior_Icc] at hx
      rw [hderiv x hx]
      exact hZ x ⟨hx.1.le, hx.2.le⟩
    · rw [Icc_self]
      exact (Set.subsingleton_singleton).strictAntiOn _
