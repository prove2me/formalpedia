-- Prove2me | solution 1 for EpiControl.SinglePeak.eq_33
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T08:08:25.639496+00:00
-- url     : https://prove2.me/submissions/6a68e46e-ccae-4a73-87b2-5676b96a3fda

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace Aux_ESP33

lemma pos_of_linear (T x0 K : ℝ) (x a : ℝ → ℝ) (hx : ContinuousOn x (Icc 0 T))
    (hx0 : 0 < x0) (hint : IntegrableOn (fun r => a r * x r) (Icc 0 T))
    (hK0 : 0 < K) (hK : ∀ r ∈ Icc 0 T, |a r| ≤ K)
    (heq : ∀ t ∈ Icc 0 T, x t = x0 + ∫ r in (0 : ℝ)..t, a r * x r) :
    ∀ t ∈ Icc 0 T, 0 < x t := by
  have hII : ∀ u ∈ Icc 0 T, ∀ v ∈ Icc 0 T,
      IntervalIntegrable (fun r => a r * x r) volume u v := fun u hu v hv =>
    (hint.mono_set (uIcc_subset_Icc hu hv)).intervalIntegrable
  by_contra hcon
  push Not at hcon
  obtain ⟨t1, ht1, hxt1⟩ := hcon
  have hT : 0 ≤ T := ht1.1.trans ht1.2
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hxz : x 0 = x0 := by
    rw [heq 0 h0mem, intervalIntegral.integral_same, add_zero]
  -- zero set
  set Z := Icc 0 T ∩ x ⁻¹' {0} with hZ
  have hZc : IsClosed Z := hx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    have hsub : Icc 0 t1 ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht1.2
    have hivt := intermediate_value_Icc' ht1.1 (hx.mono hsub)
    have h0 : (0 : ℝ) ∈ Icc (x t1) (x 0) := ⟨hxt1, by rw [hxz]; exact hx0.le⟩
    obtain ⟨c, hc, hc0⟩ := hivt h0
    exact ⟨c, hsub hc, hc0⟩
  have hZb : BddBelow Z := ⟨0, fun z hz => hz.1.1⟩
  set ts := sInf Z with hts
  have htsZ : ts ∈ Z := hZc.csInf_mem hZne hZb
  have htsT : ts ∈ Icc 0 T := htsZ.1
  have hxts : x ts = 0 := htsZ.2
  have hts0 : 0 < ts := by
    rcases eq_or_lt_of_le htsT.1 with h | h
    · rw [← h, hxz] at hxts; linarith
    · exact h
  set δ := 1 / (2 * K) with hδ
  have hδ0 : 0 < δ := by positivity
  set a0 := max 0 (ts - δ) with ha0
  have ha0lt : a0 < ts := max_lt hts0 (by linarith)
  have hWsub : Icc a0 ts ⊆ Icc 0 T := Icc_subset_Icc (le_max_left _ _) htsT.2
  -- maximum of |x| on window
  obtain ⟨tm, htm, hmax⟩ := (isCompact_Icc (a := a0) (b := ts)).exists_isMaxOn
    ⟨ts, ⟨ha0lt.le, le_rfl⟩⟩ ((hx.mono hWsub).abs)
  have hmax' : ∀ t ∈ Icc a0 ts, |x t| ≤ |x tm| := fun t ht => isMaxOn_iff.mp hmax t ht
  have hbound : ∀ t ∈ Icc a0 ts, |x t| ≤ K * |x tm| * (ts - t) := by
    intro t ht
    have htT := hWsub ht
    have hdiff : x ts - x t = ∫ r in t..ts, a r * x r := by
      rw [heq ts htsT, heq t htT, add_sub_add_left_eq_sub,
        intervalIntegral.integral_interval_sub_left (hII 0 h0mem ts htsT) (hII 0 h0mem t htT)]
    rw [hxts, zero_sub] at hdiff
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := ts) (f := fun r => a r * x r) (C := K * |x tm|) (fun r hr => by
        rw [uIoc_of_le ht.2] at hr
        have hrW : r ∈ Icc a0 ts := ⟨ht.1.trans hr.1.le, hr.2⟩
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hK r (hWsub hrW)) (hmax' r hrW) (abs_nonneg _) hK0.le)
    rw [← hdiff, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by linarith [ht.2] : 0 ≤ ts - t)] at hn
    exact hn
  have hm0 : |x tm| = 0 := by
    have h1 := hbound tm htm
    have h2 : ts - tm ≤ δ := by
      have := htm.1
      have := le_max_right 0 (ts - δ)
      linarith
    have h3 : K * |x tm| * (ts - tm) ≤ K * |x tm| * δ :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg hK0.le (abs_nonneg _))
    have h4 : K * |x tm| * δ = |x tm| / 2 := by
      rw [hδ]; field_simp
    have := abs_nonneg (x tm)
    linarith
  have hxa0 : x a0 = 0 := by
    have := hmax' a0 ⟨le_rfl, ha0lt.le⟩
    rw [hm0] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  have ha0Z : a0 ∈ Z := ⟨hWsub ⟨le_rfl, ha0lt.le⟩, hxa0⟩
  have := csInf_le hZb ha0Z
  linarith

end Aux_ESP33

open EpiControl.SinglePeak Aux_ESP33 in
theorem solution (P : Params) (hP : P.Standing) :
    (∀ x ∈ Icc (0 : ℝ) 1, x ^ 2 * (1 - x) ≤ 4 / 27) ∧
    ∀ β s i : ℝ → ℝ, P.IsOptimal β s i →
      ∀ t ∈ Icc 0 P.T, s t ^ 2 * i t ≤ s t ^ 2 * (1 - s t) ∧ s t ^ 2 * (1 - s t) ≤ 4 / 27 := by
  have poly : ∀ x : ℝ, 0 ≤ x → x ^ 2 * (1 - x) ≤ 4 / 27 := fun x hx => by
    nlinarith [mul_nonneg (sq_nonneg (x - 2 / 3)) (by linarith : (0 : ℝ) ≤ x + 1 / 3)]
  refine ⟨fun x hx => poly x hx.1, ?_⟩
  intro β s i hopt t ht
  obtain ⟨⟨hβm, hβ⟩, ⟨hs, hi, heqs⟩, -⟩ := hopt
  have hbl := hP.bl_pos
  have hbb := hP.bl_lt_bbar
  have hγ := hP.γ_pos
  obtain ⟨Ms, hMs⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.T)).exists_bound_of_continuousOn hs
  obtain ⟨Mi, hMi⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.T)).exists_bound_of_continuousOn hi
  have hsm := hs.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have him := hi.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have hβn : ∀ r ∈ Icc 0 P.T, ‖β r‖ ≤ P.bbar := fun r hr => by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [(hβ r hr).1])]; exact (hβ r hr).2
  have hMi0 : ∀ r ∈ Icc 0 P.T, 0 ≤ Mi := fun r hr => (norm_nonneg _).trans (hMi r hr)
  have hint1 : IntegrableOn (fun r => β r * i r * s r) (Icc 0 P.T) := by
    refine IntegrableOn.of_bound measure_Icc_lt_top
      ((hβm.aestronglyMeasurable.mul him).mul hsm) (P.bbar * Mi * Ms)
      (ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hβn r hr) (hMi r hr) (norm_nonneg _) (by linarith))
      (hMs r hr) (norm_nonneg _) (mul_nonneg (by linarith) (hMi0 r hr))
  have hint2 : IntegrableOn (fun r => i r) (Icc 0 P.T) := hi.integrableOn_Icc
  have hII1 : ∀ u ∈ Icc 0 P.T, IntervalIntegrable (fun r => β r * i r * s r) volume 0 u :=
    fun u hu => (hint1.mono_set (uIcc_subset_Icc ⟨le_rfl, hu.1.trans hu.2⟩ hu)).intervalIntegrable
  have hII2 : ∀ u ∈ Icc 0 P.T, IntervalIntegrable (fun r => i r) volume 0 u :=
    fun u hu => (hint2.mono_set (uIcc_subset_Icc ⟨le_rfl, hu.1.trans hu.2⟩ hu)).intervalIntegrable
  -- positivity of s
  have hspos : ∀ u ∈ Icc 0 P.T, 0 < s u := by
    refine pos_of_linear P.T P.s0 (P.bbar * Mi + 1) s (fun r => -(β r * i r)) hs
      hP.s0_mem.1 ?_ ?_ ?_ ?_
    · exact hint1.neg.congr_fun (fun r _ => by simp only [Pi.neg_apply]; ring) measurableSet_Icc
    · have := hMi0 0 ⟨le_rfl, ht.1.trans ht.2⟩
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ P.bbar) this
      linarith
    · intro r hr
      rw [abs_neg, abs_mul]
      have h1 := hβn r hr
      have h2 := hMi r hr
      rw [Real.norm_eq_abs] at h1 h2
      nlinarith [abs_nonneg (β r), abs_nonneg (i r)]
    · intro u hu
      have e : ∫ r in (0 : ℝ)..u, -(β r * i r) * s r = -∫ r in (0 : ℝ)..u, β r * i r * s r := by
        rw [← intervalIntegral.integral_neg]; congr 1; funext r; ring
      rw [e, (heqs u hu).1]; ring
  -- positivity of i
  have hipos : ∀ u ∈ Icc 0 P.T, 0 < i u := by
    refine pos_of_linear P.T P.i0 (P.bbar * Ms + P.γ + 1) i (fun r => β r * s r - P.γ) hi
      hP.i0_mem.1 ?_ ?_ ?_ ?_
    · exact (hint1.sub (hint2.const_mul P.γ)).congr_fun (fun r _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
    · have := (norm_nonneg _).trans (hMs 0 ⟨le_rfl, ht.1.trans ht.2⟩)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ P.bbar) this
      linarith
    · intro r hr
      have h1 := hβn r hr
      have h2 := hMs r hr
      rw [Real.norm_eq_abs] at h1 h2
      have h3 : |β r * s r| ≤ P.bbar * Ms := by
        rw [abs_mul]; nlinarith [abs_nonneg (β r), abs_nonneg (s r)]
      calc |β r * s r - P.γ| ≤ |β r * s r| + |P.γ| := abs_sub _ _
        _ ≤ P.bbar * Ms + P.γ + 1 := by rw [abs_of_pos hγ]; linarith
    · intro u hu
      have e : ∫ r in (0 : ℝ)..u, (β r * s r - P.γ) * i r
          = ∫ r in (0 : ℝ)..u, (β r * i r * s r - P.γ * i r) := by
        congr 1; funext r; ring
      rw [e, (heqs u hu).2]
  have hst : s t + i t ≤ 1 := by
    have hsum : s t + i t = P.s0 + P.i0 - P.γ * ∫ r in (0 : ℝ)..t, i r := by
      rw [(heqs t ht).1, (heqs t ht).2, intervalIntegral.integral_sub (hII1 t ht)
        ((hII2 t ht).const_mul P.γ), intervalIntegral.integral_const_mul]
      ring
    have hnn : 0 ≤ ∫ r in (0 : ℝ)..t, i r :=
      intervalIntegral.integral_nonneg ht.1 (fun u hu => (hipos u ⟨hu.1, hu.2.trans ht.2⟩).le)
    have := hP.s0_add_i0
    nlinarith
  have hs0 := hspos t ht
  have hi0 := hipos t ht
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  · exact poly (s t) hs0.le
