-- Prove2me | solution 1 for EpiControl.SinglePeak.proposition_2_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:22:45.131404+00:00
-- url     : https://prove2.me/submissions/aa9cc1aa-8139-4eb2-ae13-0c40f333b838

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiAuxP2i

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

end EpiAuxP2i


open EpiControl.SinglePeak in
theorem EpiAuxP2i.M_eq {P : Params} {y b : ℝ} (h : P.ArgminAt y b) :
    P.M y = y * b + P.c b := by
  unfold Params.M
  apply IsLeast.csInf_eq
  refine ⟨⟨b, h.1, rfl⟩, ?_⟩
  rintro _ ⟨b', hb', rfl⟩
  exact h.2 b' hb'

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    (∀ t ∈ Icc 0 P.T,
      HasDerivWithinAt (gain η s i)
        (-P.γ * gain η s i t + s t * (P.M (gain η s i t) - P.M (gain η s i P.T) -
          (deriv P.v (i t) * i t - P.v (i t)))) (Icc 0 P.T) t) ∧
    gain η s i P.T = 1 / P.γ * (P.v (i P.T) * s P.T) := by
  obtain ⟨hηc, hηT, heqη, hargη, hηpos⟩ := hη
  have hT : 0 ≤ P.T := hP.T_pos.le
  have hTI : P.T ∈ Icc 0 P.T := ⟨hT, le_rfl⟩
  have h0I : (0:ℝ) ∈ Icc 0 P.T := ⟨le_rfl, hT⟩
  have huIcc : uIcc 0 P.T = Icc 0 P.T := uIcc_of_le hT
  obtain ⟨hβI, hiexp, hsexp⟩ := EpiAuxP2i.path_exp hP hopt.1 hopt.2.1
  obtain ⟨hs, hi, hpath⟩ := hopt.2.1
  have hipos : ∀ r ∈ Icc 0 P.T, 0 < i r := fun r hr => by
    rw [hiexp r hr]; exact mul_pos hP.i0_mem.1 (Real.exp_pos _)
  have hiT : i P.T ≠ 0 := (hipos _ hTI).ne'
  have hgT : gain η s i P.T = P.v (i P.T) * s P.T / P.γ := by
    simp only [gain]; rw [hηT]; field_simp [hiT, hP.γ_pos.ne']
  refine ⟨?_, by rw [hgT]; ring⟩
  have hdv : Continuous (deriv P.v) := hP.v_C1.continuous_deriv le_rfl
  have hvc : Continuous P.v := hP.v_C1.continuous
  have hMc : Continuous P.M := (EpiAuxP2i.M_lip hP).continuous
  set MT := P.M (P.v (i P.T) * s P.T / P.γ) with hMT
  set hfun : ℝ → ℝ := fun r => η r * β r * i r - deriv P.v (i r) +
    (P.v (i r) + P.c (β r) - MT) / i r with hhfun
  -- integrability of c ∘ β
  set clampB : ℝ → ℝ := fun b => max P.bl (min b P.bbar) with hclampB
  have hclampBc : Continuous clampB := continuous_const.max (continuous_id.min continuous_const)
  have hclampBI : ∀ b, clampB b ∈ Icc P.bl P.bbar := fun b =>
    ⟨le_max_left _ _, max_le hP.bl_lt_bbar.le (min_le_right _ _)⟩
  have hct : Continuous (fun b => P.c (clampB b)) := hP.c_cont.comp_continuous hclampBc hclampBI
  obtain ⟨Cc, hCc⟩ := isCompact_Icc.exists_bound_of_continuousOn hP.c_cont
  have hcβI : IntervalIntegrable (fun r => P.c (β r)) volume 0 P.T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    have h1 : IntegrableOn (fun r => P.c (clampB (β r))) (Icc 0 P.T) volume := by
      refine Measure.integrableOn_of_bounded (M := Cc) (by simp)
        (hct.measurable.comp hopt.1.1).aestronglyMeasurable ?_
      exact Eventually.of_forall fun r => hCc _ (hclampBI _)
    refine h1.congr_fun (fun r hr => ?_) measurableSet_Icc
    have hb := hopt.1.2 r hr
    simp only [hclampB, min_eq_left hb.2, max_eq_right hb.1]
  have hinvI : ContinuousOn (fun r => 1 / i r) (Icc 0 P.T) :=
    continuousOn_const.div hi (fun r hr => (hipos r hr).ne')
  have hhI : IntervalIntegrable hfun volume 0 P.T := by
    have e : hfun = fun r => (β r * (η r * i r) - deriv P.v (i r) + (P.v (i r) - MT) * (1 / i r))
        + P.c (β r) * (1 / i r) := by
      funext r; simp only [hhfun]; ring
    rw [e]
    refine IntervalIntegrable.add ?_ ?_
    · refine IntervalIntegrable.add (IntervalIntegrable.sub ?_ ?_) ?_
      · exact hβI.mul_continuousOn (by rw [huIcc]; exact hηc.mul hi)
      · exact ContinuousOn.intervalIntegrable (by rw [huIcc]; exact hdv.comp_continuousOn hi)
      · exact ContinuousOn.intervalIntegrable (by
          rw [huIcc]; exact ((hvc.comp_continuousOn hi).sub continuousOn_const).mul hinvI)
    · exact hcβI.mul_continuousOn (by rw [huIcc]; exact hinvI)
  have hsub0 : ∀ t ∈ Icc 0 P.T, uIcc 0 t ⊆ uIcc 0 P.T := fun t ht => by
    rw [huIcc, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hsubT : ∀ t ∈ Icc 0 P.T, uIcc t P.T ⊆ uIcc 0 P.T := fun t ht => by
    rw [huIcc, uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl
  -- forward integral forms
  have hηfwd : ∀ t ∈ Icc 0 P.T, η t = η 0 + ∫ r in (0:ℝ)..t, hfun r := by
    intro t ht
    have e0 := heqη 0 h0I
    have et := heqη t ht
    have := intervalIntegral.integral_add_adjacent_intervals (hhI.mono_set (hsub0 t ht))
      (hhI.mono_set (hsubT t ht))
    linarith
  set fi : ℝ → ℝ := fun r => β r * i r * s r - P.γ * i r with hfi
  set fs : ℝ → ℝ := fun r => β r * i r * s r with hfs
  have hfsI : IntervalIntegrable fs volume 0 P.T := by
    have : fs = fun r => β r * (i r * s r) := by funext r; simp only [hfs]; ring
    rw [this]; exact hβI.mul_continuousOn (by rw [huIcc]; exact hi.mul hs)
  have hfiI : IntervalIntegrable fi volume 0 P.T :=
    hfsI.sub (ContinuousOn.intervalIntegrable (by rw [huIcc]; exact continuousOn_const.mul hi))
  set ηp : ℝ → ℝ := fun t => η 0 + ∫ r in (0:ℝ)..t, hfun r with hηp
  set ip : ℝ → ℝ := fun t => P.i0 + ∫ r in (0:ℝ)..t, fi r with hip
  set sp : ℝ → ℝ := fun t => P.s0 - ∫ r in (0:ℝ)..t, fs r with hsp
  have hACconst : ∀ c : ℝ, AbsolutelyContinuousOnInterval (fun _ => c) 0 P.T := fun c =>
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  have acη : AbsolutelyContinuousOnInterval ηp 0 P.T :=
    (hACconst _).fun_add (hhI.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have aci : AbsolutelyContinuousOnInterval ip 0 P.T :=
    (hACconst _).fun_add (hfiI.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have acs : AbsolutelyContinuousOnInterval sp 0 P.T :=
    (hACconst _).fun_sub (hfsI.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  set gp : ℝ → ℝ := fun t => ηp t * ip t * sp t with hgp
  have acg : AbsolutelyContinuousOnInterval gp 0 P.T := (acη.fun_mul aci).fun_mul acs
  have hgeq : ∀ t ∈ Icc 0 P.T, gain η s i t = gp t := by
    intro t ht
    simp only [gain, hgp, hηp, hip, hsp]
    rw [← hηfwd t ht, ← (hpath t ht).1, ← (hpath t ht).2]
  set G1 : ℝ → ℝ := fun t => -P.γ * gain η s i t + s t * (P.M (gain η s i t) -
      P.M (gain η s i P.T) - (deriv P.v (i t) * i t - P.v (i t))) with hG1
  -- a.e. derivative
  have hargη' := (ae_restrict_iff' measurableSet_Icc).1 hargη
  have hderiv : ∀ᵐ t, t ∈ uIcc 0 P.T → HasDerivAt gp (G1 t) t := by
    filter_upwards [hhI.ae_hasDerivAt_integral, hfiI.ae_hasDerivAt_integral,
      hfsI.ae_hasDerivAt_integral, hargη'] with t h1 h2 h3 harg ht
    have d1 : HasDerivAt ηp (hfun t) t := (h1 ht 0 (by simp)).const_add _
    have d2 : HasDerivAt ip (fi t) t := (h2 ht 0 (by simp)).const_add _
    have d3 : HasDerivAt sp (-fs t) t := (h3 ht 0 (by simp)).const_sub _
    refine ((d1.fun_mul d2).fun_mul d3).congr_deriv ?_
    rw [huIcc] at ht
    have hgt := hgeq t ht
    simp only [gain] at hgt
    have eη : ηp t = η t := (hηfwd t ht).symm
    have ei : ip t = i t := ((hpath t ht).2).symm
    have es : sp t = s t := ((hpath t ht).1).symm
    rw [eη, ei, es]
    have hMg : P.M (gain η s i t) = gain η s i t * β t + P.c (β t) :=
      EpiAuxP2i.M_eq (harg ht)
    have hMgT : P.M (gain η s i P.T) = MT := by rw [hgT]
    have hit := (hipos t ht).ne'
    simp only [hG1]
    rw [hMg, hMgT]
    simp only [gain, hhfun, hfi, hfs]
    field_simp
    ring
  have hgc : ContinuousOn (gain η s i) (Icc 0 P.T) := (hηc.mul hi).mul hs
  have hG1c : ContinuousOn G1 (Icc 0 P.T) := by
    apply ContinuousOn.add (continuousOn_const.mul hgc)
    apply hs.mul
    apply ContinuousOn.sub (ContinuousOn.sub (hMc.comp_continuousOn hgc) continuousOn_const)
    exact ((hdv.comp_continuousOn hi).mul hi).sub (hvc.comp_continuousOn hi)
  set clamp : ℝ → ℝ := fun t => max 0 (min t P.T) with hclamp
  have hclampI : ∀ t, clamp t ∈ Icc 0 P.T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclampid : ∀ t ∈ Icc 0 P.T, clamp t = t := fun t ht => by
    simp only [hclamp]; rw [min_eq_left ht.2, max_eq_right ht.1]
  have hcl : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  set Gt : ℝ → ℝ := fun t => G1 (clamp t) with hGt
  have hGtc : Continuous Gt := hG1c.comp_continuous hcl hclampI
  have rep : ∀ t ∈ Icc 0 P.T, gain η s i t = gain η s i 0 + ∫ r in (0:ℝ)..t, Gt r := by
    intro t ht
    have hFTC := (acg.mono (hsub0 t ht)).integral_deriv_eq_sub
    have hcongr : (∫ r in (0:ℝ)..t, deriv gp r) = ∫ r in (0:ℝ)..t, Gt r := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with x hx hxI
      rw [uIoc_of_le ht.1] at hxI
      have hxT : x ∈ Icc 0 P.T := ⟨hxI.1.le, hxI.2.trans ht.2⟩
      rw [(hx (by rw [huIcc]; exact hxT)).deriv]
      simp only [hGt, hclampid x hxT]
    rw [hgeq t ht, hgeq 0 h0I]
    linarith
  intro t ht
  have HF : HasDerivAt (fun u => gain η s i 0 + ∫ r in (0:ℝ)..u, Gt r) (Gt t) t :=
    (hGtc.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _
  have H := HF.hasDerivWithinAt (s := Icc 0 P.T) |>.congr (fun u hu => rep u hu) (rep t ht)
  have e : Gt t = G1 t := by simp only [hGt, hclampid t ht]
  rw [e] at H
  exact H
