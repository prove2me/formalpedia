-- Prove2me | solution 1 for EpiControl.SinglePeak.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:32:19.869343+00:00
-- url     : https://prove2.me/submissions/9f6e5cca-cffc-4be6-b040-335686bcc075

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model
import Theorems.Thm_EpiControl_SinglePeak_proposition_2_i
import Theorems.Thm_EpiControl_SinglePeak_eq_33

open MeasureTheory Set Filter Topology

namespace EpiAux37

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

end EpiAux37


namespace EpiAux37

theorem alg_ineq (γ g s i β w C G dc bl bb vp Y : ℝ) (hg : 0 < g) (hβ : 0 < β) (hi : 0 < i)
    (hs : 0 ≤ s) (hw : 0 ≤ w) (hdc : dc < 0) (hbl : 0 < bl)
    (hG : G = -γ * g + s * (g * β + C)) (his : i * s ^ 2 ≤ 4 / 27)
    (hY : Y = (bb - bl) / (bl * (-dc))) (hY0 : 0 ≤ Y) (hX : C / (β * g ^ 2) ≤ Y) :
    -γ * G + ((-(β * i * s)) * (g * β + C) + s * (β * G - (w * (β * i * s - γ * i) * i +
      vp * (β * i * s - γ * i) - vp * (β * i * s - γ * i)))) ≤
    (-γ + β * (s - i) - w * i ^ 2 * s / g) * G -
      g * β * i * (4 * w / (27 * dc) * (bb / bl - 1) + γ) := by
  set X := C / (β * g ^ 2) with hXdef
  have hdc' : dc ≠ 0 := hdc.ne
  have key : -γ * G + ((-(β * i * s)) * (g * β + C) + s * (β * G - (w * (β * i * s - γ * i) * i +
      vp * (β * i * s - γ * i) - vp * (β * i * s - γ * i)))) -
      ((-γ + β * (s - i) - w * i ^ 2 * s / g) * G -
        g * β * i * (4 * w / (27 * dc) * (bb / bl - 1) + γ)) =
      g * β * i * (w * (i * s ^ 2 * X) + 4 * w / (27 * dc) * (bb / bl - 1)) := by
    rw [hXdef, hG]
    field_simp
    ring
  have hYeq : 4 / 27 * Y = -(4 / (27 * dc) * (bb / bl - 1)) := by
    rw [hY]; field_simp
  have h1 : i * s ^ 2 * X ≤ 4 / 27 * Y := by
    rcases le_or_gt X 0 with h | h
    · have : i * s ^ 2 * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
      linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 4 / 27) hY0]
    · calc i * s ^ 2 * X ≤ 4 / 27 * X := mul_le_mul_of_nonneg_right his h.le
        _ ≤ 4 / 27 * Y := mul_le_mul_of_nonneg_left hX (by norm_num)
  have h2 : w * (i * s ^ 2 * X) + 4 * w / (27 * dc) * (bb / bl - 1) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h1 hw
    have e : 4 * w / (27 * dc) * (bb / bl - 1) = w * (4 / (27 * dc) * (bb / bl - 1)) := by ring
    rw [e]
    nlinarith
  have h3 : 0 < g * β * i := by positivity
  have := mul_nonpos_of_nonneg_of_nonpos h3.le h2
  linarith

end EpiAux37

open EpiControl.SinglePeak in
theorem EpiAux37.M_eq {P : Params} {y b : ℝ} (h : P.ArgminAt y b) :
    P.M y = y * b + P.c b := by
  unfold Params.M
  apply IsLeast.csInf_eq
  refine ⟨⟨b, h.1, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩
  exact h.2 b' hb'

open EpiControl.SinglePeak in
/-- Supergradient inequality for `M`. -/
theorem EpiAux37.M_sup {P : Params} (hP : P.Standing) {y b : ℝ} (h : P.ArgminAt y b)
    (y' : ℝ) : P.M y' ≤ P.M y + (y' - y) * b := by
  have hf2 : ContinuousOn (fun b => y' * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  have hbdd : BddBelow ((fun b => y' * b + P.c b) '' Icc P.bl P.bbar) :=
    (isCompact_Icc.image_of_continuousOn hf2).bddBelow
  have h1 : P.M y' ≤ y' * b + P.c b := csInf_le hbdd ⟨b, h.1, rfl⟩
  rw [EpiAux37.M_eq h]
  linarith

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (dc : ℝ) (hA1 : P.Assumption1 dc)
    (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    let g : ℝ → ℝ := gain η s i
    let G1 : ℝ → ℝ := fun t =>
      -P.γ * g t + s t * (P.M (g t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t)))
    ∀ᵐ t ∂(volume.restrict (Icc 0 P.T)),
      DifferentiableAt ℝ G1 t ∧
      deriv G1 t ≤
        (-P.γ + β t * (s t - i t) - deriv (deriv P.v) (i t) * i t ^ 2 * s t / g t) * G1 t -
          g t * β t * i t *
            (4 * deriv (deriv P.v) (i t) / (27 * dc) * (P.bbar / P.bl - 1) + P.γ) := by
  intro g G1
  obtain ⟨hgd, _⟩ := proposition_2_i P hP β s i hopt η hη
  have hT0 : 0 < P.T := hP.T_pos
  have hT : 0 ≤ P.T := hT0.le
  have hTI : P.T ∈ Icc 0 P.T := ⟨hT, le_rfl⟩
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  obtain ⟨hβI, hiexp, hsexp⟩ := EpiAux37.path_exp hP hopt.1 hopt.2.1
  obtain ⟨hs, hi, hpath⟩ := hopt.2.1
  have hipos : ∀ r ∈ Icc 0 P.T, 0 < i r := fun r hr => by
    rw [hiexp r hr]; exact mul_pos hP.i0_mem.1 (Real.exp_pos _)
  have hspos : ∀ r ∈ Icc 0 P.T, 0 < s r := fun r hr => by
    rw [hsexp r hr]; exact mul_pos hP.s0_mem.1 (Real.exp_pos _)
  have h33 := fun r hr => (eq_33 P hP).2 β s i hopt r hr
  have his1 : ∀ r ∈ Icc 0 P.T, i r + s r ≤ 1 := by
    intro r hr
    have h := (h33 r hr).1
    have hs2 : 0 < s r ^ 2 := by have := hspos r hr; positivity
    have := le_of_mul_le_mul_left h hs2
    linarith
  have hi1 : ∀ r ∈ Icc 0 P.T, i r < 1 := fun r hr => by linarith [his1 r hr, hspos r hr]
  have hβB : ∀ r ∈ Icc 0 P.T, β r ∈ Icc P.bl P.bbar := hopt.1.2
  have hgpos : ∀ r ∈ Icc 0 P.T, 0 < g r := fun r hr =>
    mul_pos (mul_pos (hη.2.2.2.2 r hr) (hipos r hr)) (hspos r hr)
  -- smoothness of v
  have hv2 : ContDiff ℝ (1 + 1) P.v := hA1.1
  have hdv1 : ContDiff ℝ 1 (deriv P.v) := (contDiff_succ_iff_deriv.1 hv2).2.2
  have hdv_diff : Differentiable ℝ (deriv P.v) := hdv1.differentiable one_ne_zero
  have hdv : Continuous (deriv P.v) := hdv1.continuous
  have hv_diff : Differentiable ℝ P.v := hP.v_C1.differentiable one_ne_zero
  have hvc : Continuous P.v := hP.v_C1.continuous
  -- v'' ≥ 0 on (0,1)
  have hmono : MonotoneOn (deriv P.v) (Icc 0 1) :=
    hP.v_convex.monotoneOn_deriv (fun y _ => hv_diff y)
  have hw0 : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ deriv (deriv P.v) x := by
    intro x hx
    have hd := (hdv_diff x).hasDerivAt.hasDerivWithinAt (s := Ioi x)
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
    apply ge_of_tendsto hd
    filter_upwards [Ioo_mem_nhdsGT hx.2] with y hy
    rw [slope_def_field]
    apply div_nonneg _ (by linarith [hy.1])
    have := hmono ⟨hx.1.le, hx.2.le⟩ ⟨by linarith [hy.1, hx.1], hy.2.le⟩ hy.1.le
    linarith
  -- dc < 0
  have hdcle : dc ≤ 0 := by
    apply le_of_tendsto hA1.2.1
    filter_upwards [Ioo_mem_nhdsLT hP.bl_lt_bbar] with b hb
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith [hb.2])
    have := hP.c_antitone ⟨hb.1.le, hb.2.le⟩ ⟨hP.bl_lt_bbar.le, le_rfl⟩ hb.2.le
    linarith
  have hdc : dc < 0 := by
    rcases hdcle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hA := hA1.2.2 (1/2) ⟨by norm_num, by norm_num⟩
      rw [h, abs_zero, mul_zero] at hA
      have := hw0 (1/2) ⟨by norm_num, by norm_num⟩
      have := div_nonneg this hP.γ_pos.le
      linarith
  -- slope bound from convexity: c(b) ≥ -dc (bbar - b)
  have hslope : ∀ b ∈ Ico P.bl P.bbar, -dc * (P.bbar - b) ≤ P.c b := by
    intro b hb
    have hq : (P.c P.bbar - P.c b) / (P.bbar - b) ≤ dc := by
      apply ge_of_tendsto hA1.2.1
      filter_upwards [Ioo_mem_nhdsLT hb.2] with b' hb'
      have := hP.c_convex.secant_mono (a := P.bbar) (x := b) (y := b')
        ⟨hP.bl_lt_bbar.le, le_rfl⟩ ⟨hb.1, hb.2.le⟩ ⟨by linarith [hb.1, hb'.1], hb'.2.le⟩
        hb.2.ne hb'.2.ne hb'.1.le
      rw [show P.c b - P.c P.bbar = -(P.c P.bbar - P.c b) by ring,
        show b - P.bbar = -(P.bbar - b) by ring, neg_div_neg_eq,
        show P.c b' - P.c P.bbar = -(P.c P.bbar - P.c b') by ring,
        show b' - P.bbar = -(P.bbar - b') by ring, neg_div_neg_eq] at this
      exact this
    rw [div_le_iff₀ (by linarith [hb.2]), hP.c_bbar] at hq
    linarith
  have hargbar : ∀ y b, P.ArgminAt y b → y < -dc → b = P.bbar := by
    intro y b hab hy
    by_contra hne
    have hb : b ∈ Ico P.bl P.bbar := ⟨hab.1.1, lt_of_le_of_ne hab.1.2 hne⟩
    have h1 := hslope b hb
    have h2 := hab.2 P.bbar ⟨hP.bl_lt_bbar.le, le_rfl⟩
    rw [hP.c_bbar] at h2
    have : y * (P.bbar - b) < -dc * (P.bbar - b) :=
      mul_lt_mul_of_pos_right hy (by linarith [hb.2])
    nlinarith
  -- tangent inequality: Q ≥ 0
  have hQ0 : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ deriv P.v x * x - P.v x := by
    intro x hx
    have := hP.v_convex.slope_le_deriv (x := 0) (y := x) ⟨le_rfl, zero_le_one⟩
      ⟨hx.1.le, hx.2.le⟩ hx.1 (hv_diff x)
    rw [slope_def_field, hP.v_zero, sub_zero, sub_zero, div_le_iff₀ hx.1] at this
    linarith
  -- continuity and Lipschitz properties
  have hMl := EpiAux37.M_lip hP
  have hMc : Continuous P.M := hMl.continuous
  have hgc : ContinuousOn g (Icc 0 P.T) := fun r hr => (hgd r hr).continuousWithinAt
  have hG1c : ContinuousOn G1 (Icc 0 P.T) := by
    apply ContinuousOn.add (continuousOn_const.mul hgc)
    apply hs.mul
    apply ContinuousOn.sub (ContinuousOn.sub (hMc.comp_continuousOn hgc) continuousOn_const)
    exact ((hdv.comp_continuousOn hi).mul hi).sub (hvc.comp_continuousOn hi)
  obtain ⟨CG, hCG⟩ := isCompact_Icc.exists_bound_of_continuousOn hG1c
  have hCG0 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG 0 ⟨le_rfl, hT⟩)
  have hglip : LipschitzOnWith (Real.toNNReal CG) g (Icc 0 P.T) := by
    apply (convex_Icc 0 P.T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hgd
    intro x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hCG0]
    exact hCG x hx
  have hMgac : AbsolutelyContinuousOnInterval (fun u => P.M (g u)) 0 P.T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [huIcc]
    exact (hMl.lipschitzOnWith (s := univ)).comp hglip (mapsTo_univ _ _)
  have hMgd := hMgac.ae_differentiableAt
  set fs : ℝ → ℝ := fun r => β r * i r * s r with hfs
  set fi : ℝ → ℝ := fun r => β r * i r * s r - P.γ * i r with hfi
  have hfsI : IntervalIntegrable fs volume 0 P.T := by
    have : fs = fun r => β r * (i r * s r) := by funext r; simp only [hfs]; ring
    rw [this]; exact hβI.mul_continuousOn (by rw [huIcc]; exact hi.mul hs)
  have hfiI : IntervalIntegrable fi volume 0 P.T :=
    hfsI.sub (ContinuousOn.intervalIntegrable (by rw [huIcc]; exact continuousOn_const.mul hi))
  have hfsD := hfsI.ae_hasDerivAt_integral
  have hfiD := hfiI.ae_hasDerivAt_integral
  have hne0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hneT : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ P.T := by simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hMgd,
    ae_restrict_of_ae hfsD, ae_restrict_of_ae hfiD, ae_restrict_of_ae hne0,
    ae_restrict_of_ae hneT] with t htI hMd hsD hiD ht0 htT
  have htIoo : t ∈ Ioo 0 P.T := ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), lt_of_le_of_ne htI.2 htT⟩
  have hnhds : Icc 0 P.T ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
  have htu : t ∈ uIcc 0 P.T := by rw [huIcc]; exact htI
  have hg' : HasDerivAt g (G1 t) t := (hgd t htI).hasDerivAt hnhds
  have hs' : HasDerivAt s (-(β t * i t * s t)) t := by
    have h := (hsD htu 0 (by simp)).const_sub P.s0
    exact h.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hnhds (fun u hu => (hpath u hu).1))
  have hi' : HasDerivAt i (β t * i t * s t - P.γ * i t) t := by
    have h := (hiD htu 0 (by simp)).const_add P.i0
    exact h.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hnhds (fun u hu => (hpath u hu).2))
  have hMg' : HasDerivAt (fun u => P.M (g u)) (β t * G1 t) t := by
    have hd := hMd htu
    have hφ := hd.hasDerivAt.sub (hg'.const_mul (β t))
    have hmax : IsLocalMax (fun u => P.M (g u) - β t * g u) t := by
      refine Filter.Eventually.of_forall (fun u => ?_)
      have := EpiAux37.M_sup hP (hconv t htI) (g u)
      show P.M (g u) - β t * g u ≤ P.M (g t) - β t * g t
      have e : P.M (gain η s i t) = P.M (g t) := rfl
      have e2 : gain η s i t = g t := rfl
      rw [e, e2] at this
      linarith
    have h0 := hmax.hasDerivAt_eq_zero hφ
    have e : deriv (fun u => P.M (g u)) t = β t * G1 t := by linarith
    rw [← e]; exact hd.hasDerivAt
  have hQ' := (((hdv_diff (i t)).hasDerivAt.comp t hi').mul hi').sub
    ((hv_diff (i t)).hasDerivAt.comp t hi')
  have hG1' := (hg'.const_mul (-P.γ)).add (hs'.mul ((hMg'.sub_const (P.M (g P.T))).sub hQ'))
  replace hG1' : HasDerivAt G1 _ t := hG1'
  refine ⟨hG1'.differentiableAt, ?_⟩
  rw [hG1'.deriv]
  -- algebra
  have hgt := hgpos t htI
  have hit := hipos t htI
  have hst := hspos t htI
  have hβt : 0 < β t := lt_of_lt_of_le hP.bl_pos (hβB t htI).1
  have hitI : i t ∈ Ioo (0:ℝ) 1 := ⟨hit, hi1 t htI⟩
  set C := P.c (β t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t)) with hC
  have hMgt : P.M (g t) = g t * β t + P.c (β t) := EpiAux37.M_eq (hconv t htI)
  have hB : P.M (g t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t)) = g t * β t + C := by
    rw [hMgt, hC]; ring
  have hG : G1 t = -P.γ * g t + s t * (g t * β t + C) := by
    show -P.γ * g t + s t * (P.M (g t) - P.M (g P.T) - (deriv P.v (i t) * i t - P.v (i t))) = _
    rw [hB]
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
  rw [hB]
  set Y := (P.bbar - P.bl) / (P.bl * (-dc)) with hY
  have hbl := hP.bl_pos
  have hY0 : 0 ≤ Y := div_nonneg (by linarith [hP.bl_lt_bbar]) (by nlinarith)
  -- C ≤ (β T - β t) g t
  have hC1 : C ≤ (β P.T - β t) * g t := by
    have hsupT := EpiAux37.M_sup hP (hconv P.T hTI) (g t)
    have e : P.M (gain η s i P.T) = P.M (g P.T) := rfl
    have e2 : gain η s i P.T = g P.T := rfl
    rw [e, e2] at hsupT
    have hQ := hQ0 (i t) hitI
    have hgTβ : 0 ≤ g P.T * β P.T :=
      mul_nonneg (hgpos P.T hTI).le (le_trans hbl.le (hβB P.T hTI).1)
    rw [hC]
    nlinarith
  have hX : C / (β t * g t ^ 2) ≤ Y := by
    rcases lt_or_ge (g t) (-dc) with hlt | hge
    · have hβbar : β t = P.bbar := hargbar _ _ (hconv t htI) hlt
      have : C ≤ 0 := by
        have := (hβB P.T hTI).2
        rw [hβbar] at hC1
        nlinarith
      exact le_trans (div_nonpos_of_nonpos_of_nonneg this (by positivity)) hY0
    · rw [div_le_iff₀ (by positivity)]
      have h1 : C ≤ (P.bbar - P.bl) * g t := by
        have := (hβB P.T hTI).2
        have := (hβB t htI).1
        nlinarith
      have h2 : P.bl * (-dc) ≤ β t * g t :=
        mul_le_mul (hβB t htI).1 hge (by linarith) hβt.le
      have h3 : (P.bbar - P.bl) * g t * (P.bl * (-dc)) ≤ (P.bbar - P.bl) * (β t * g t ^ 2) := by
        have := mul_le_mul_of_nonneg_left h2
          (mul_nonneg (sub_nonneg.2 hP.bl_lt_bbar.le) hgt.le : 0 ≤ (P.bbar - P.bl) * g t)
        nlinarith
      have h4 : (P.bbar - P.bl) * g t ≤ Y * (β t * g t ^ 2) := by
        rw [hY, div_mul_eq_mul_div, le_div_iff₀ (by nlinarith)]
        exact h3
      linarith
  have his : i t * s t ^ 2 ≤ 4 / 27 := by
    have := h33 t htI
    nlinarith [this.1, this.2]
  exact EpiAux37.alg_ineq P.γ (g t) (s t) (i t) (β t) (deriv (deriv P.v) (i t)) C (G1 t) dc
    P.bl P.bbar (deriv P.v (i t)) Y hgt hβt hit hst.le (hw0 (i t) hitI) hdc hbl hG his hY hY0 hX
