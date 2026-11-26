-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.discounted_cost_of_queue_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:43:37.323813+00:00
-- url     : https://prove2.me/submissions/06d6a857-413c-43a5-8c4f-f870e99a26e3

import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
import Theorems.Thm_ManyServerQED_Scheduling_nonnegative_cost_expectation_from_ae_limit_and_moment

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BellWilliams2001.ThresholdPolicy

private theorem count_right {e : ℕ → ℝ} (hm : StrictMono e) (h0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop) {t : ℝ} (ht : 0 ≤ t) :
    ∃ b : ℝ, t < b ∧ ∀ s ∈ Ico t b, renewalCount e s = renewalCount e t := by
  have hex : ∃ i, t < e i := (hUnbounded.eventually_gt_atTop t).exists
  let i := Nat.find hex
  have hi : t < e i := Nat.find_spec hex
  have hi0 : i ≠ 0 := fun he => by simpa [he, h0, not_lt.mpr ht] using hi
  let j := i - 1
  have hij : j + 1 = i := by dsimp [j]; omega
  have hj : e j ≤ t := le_of_not_gt (Nat.find_min hex (by omega : j < i))
  have count_eq (s : ℝ) (h₁ : t ≤ s) (h₂ : s < e i) : renewalCount e s = j := by
    unfold renewalCount
    refine le_antisymm (iSup_le fun k => iSup_le fun hk => ?_) ?_
    · have hk' : k ≤ j := by
        by_contra! h
        exact (h₂.trans_le (hm.monotone (by omega : i ≤ k))).not_ge hk
      exact_mod_cast hk'
    · exact le_iSup_of_le j (le_iSup_of_le (hj.trans h₁) le_rfl)
  exact ⟨e i, hi, fun s hs => (count_eq s hs.1 hs.2).trans (count_eq t le_rfl hi).symm⟩

private theorem count_comp_right {e : ℕ → ℝ} (hm : StrictMono e) (h0 : e 0 = 0)
    (hUnbounded : Tendsto e atTop atTop) {v : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ v t)
    (hc : ContinuousWithinAt v (Ici t) t) (hv : ∀ s ∈ Ici t, v t ≤ v s) :
    ContinuousWithinAt (fun s => ((renewalCount e (v s)).toNat : ℝ)) (Ici t) t := by
  obtain ⟨b,hb,hcount⟩ := count_right hm h0 hUnbounded ht
  have h : ∀ᶠ s in 𝓝[Ici t] t, v s < b := hc.eventually (gt_mem_nhds hb)
  have hs : ∀ᶠ s in 𝓝[Ici t] t, s ∈ Ici t := self_mem_nhdsWithin
  have he : (fun s => ((renewalCount e (v s)).toNat : ℝ)) =ᶠ[𝓝[Ici t] t]
      (fun _ => ((renewalCount e (v t)).toNat : ℝ)) := by
    filter_upwards [h,hs] with s hsb hst
    rw [hcount (v s) ⟨hv s hst,hsb⟩]
  exact tendsto_const_nhds.congr' he.symm

private theorem scaled_epochs {f : ℕ → ℝ} (hf : ∀ j, 1 ≤ j → 0 < f j)
    (hlim : Tendsto (partialSum f) atTop atTop) {a : ℝ} (ha : 0 < a) :
    let e := partialSum (fun j => f j / a)
    StrictMono e ∧ e 0 = 0 ∧ Tendsto e atTop atTop := by
  have hcongr (j : ℕ) : partialSum (fun i => f i / a) j = (partialSum f j) / a := by
    simp [partialSum, Finset.sum_div]
  have hMono : StrictMono (partialSum f) := strictMono_nat_of_lt_succ fun j => by
    have he : Finset.Icc 1 (j+1) = insert (j+1) (Finset.Icc 1 j) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [partialSum, partialSum, he, Finset.sum_insert (by simp)]
    linarith [hf (j+1) (by omega)]
  refine ⟨fun i j hij => ?_, by simp [partialSum], ?_⟩
  · simp only [hcongr]
    exact div_lt_div_of_pos_right (hMono hij) ha
  · exact (hlim.atTop_div_const ha).congr (fun j => (hcongr j).symm)

private theorem queue_right {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω) (k : Fin 2)
    (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (fun s => M.Qhat n T ω s k) (Ici t) t := by
  have aRight (i : Fin 2) (u : ℝ) (hu : 0 ≤ u) :
      ContinuousWithinAt (M.A n i ω) (Ici u) u := by
    obtain ⟨hm,h0,hUnbounded⟩ := scaled_epochs (fun j => M.uC_pos i j ω) (M.uC_finite i ω) (M.lamR_pos n i)
    exact count_comp_right hm h0 hUnbounded hu continuous_id.continuousWithinAt (fun _ hs => hs)
  have sRight (j : Fin 3) (u : ℝ) (hu : 0 ≤ u) :
      ContinuousWithinAt (fun v => M.S n j ω (T ω j v)) (Ici u) u := by
    obtain ⟨hm,h0,hUnbounded⟩ := scaled_epochs (fun i => M.vC_pos j i ω) (M.vC_finite j ω) (M.muR_pos n j)
    have hNon := hT.alloc_mono ω j (show (0 : ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl)
      (show u ∈ Ici 0 from hu) hu
    rw [hT.alloc_zero ω j] at hNon
    have hcont := (hT.alloc_cont ω j u hu).mono (fun s hs => hu.trans hs)
    exact count_comp_right hm h0 hUnbounded hNon hcont
      (fun v hv => hT.alloc_mono ω j hu (hu.trans hv) hv)
  let R := M.r n ^ 2
  have hR : 0 ≤ R := sq_nonneg _
  have hRt : 0 ≤ R*t := mul_nonneg hR ht
  have hq : ContinuousWithinAt (M.queue n T ω k) (Ici (R*t)) (R*t) := by
    change ContinuousWithinAt (fun u => M.queue n T ω k u) (Ici (R*t)) (R*t)
    by_cases hk : k = 0
    · simpa only [SystemSequence.queue, if_pos hk, Pi.sub_def] using
        ((aRight 0 _ hRt).sub (sRight 0 _ hRt)).sub (sRight 1 _ hRt)
    · simpa only [SystemSequence.queue, if_neg hk, Pi.sub_def] using
        (aRight 1 _ hRt).sub (sRight 2 _ hRt)
  have hRcont : ContinuousWithinAt (fun v : ℝ => R * v) (Ici t) t :=
    (continuous_const.mul continuous_id).continuousWithinAt
  have hMap : MapsTo (fun v : ℝ => R * v) (Ici t) (Ici (R*t)) :=
    fun v hv => mul_le_mul_of_nonneg_left hv hR
  exact (hq.comp hRcont hMap).div_const _

private theorem past_inf_right (x : ℝ → ℝ) (hx : Continuous x) (t : ℝ) (ht : 0 ≤ t) :
    ContinuousWithinAt (fun u : ℝ => ⨅ s : Icc (0 : ℝ) u, x s) (Ici t) t := by
  let f (u : ℝ) := ⨅ s : Icc (0 : ℝ) u, x s
  have hb (u : ℝ) : BddBelow (range (fun s : Icc (0 : ℝ) u => x s)) := by
    rw [← Set.image_eq_range]
    exact ((isCompact_Icc (a := (0 : ℝ)) (b := u)).image hx).bddBelow
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hnear := (Metric.tendsto_nhds.1 (hx.tendsto t)) (ε/2) (by positivity)
  obtain ⟨δ,hδ,hδspec⟩ := Metric.eventually_nhds_iff.1 hnear
  have hInterval : ∀ᶠ u in 𝓝[Ici t] t, u ∈ Ici t ∧ dist u t < δ :=
    eventually_mem_nhdsWithin.and (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hδ))
  filter_upwards [hInterval] with u hu
  have hu0 : 0 ≤ u := ht.trans hu.1
  letI : Nonempty (Icc (0 : ℝ) u) := ⟨⟨0,le_rfl,hu0⟩⟩
  letI : Nonempty (Icc (0 : ℝ) t) := ⟨⟨0,le_rfl,ht⟩⟩
  have hUpper : f u ≤ f t := le_ciInf fun s : Icc (0 : ℝ) t =>
    ciInf_le (hb u) ⟨s, s.2.1, s.2.2.trans hu.1⟩
  have hLower : f t - ε/2 ≤ f u := le_ciInf fun s : Icc (0 : ℝ) u => by
    by_cases hst : (s : ℝ) ≤ t
    · exact (sub_le_self _ (by positivity)).trans (ciInf_le (hb t) ⟨s,s.2.1,hst⟩)
    · have hst' : t ≤ (s : ℝ) := (lt_of_not_ge hst).le
      have hdist : dist (s : ℝ) t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst')]
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1)] at hu
        linarith [s.2.2]
      have hnear' := hδspec hdist
      rw [Real.dist_eq] at hnear'
      have htx : f t ≤ x t := ciInf_le (hb t) ⟨t,ht,le_rfl⟩
      linarith [(abs_lt.1 hnear').1]
  change dist (f u) (f t) < ε
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 hUpper)]
  linarith

private theorem qstar_right_ae {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (M : SystemSequence Ω) (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B) :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (fun s => M.Qstar B ω s 1) (Ici t) t := by
  filter_upwards [ae_all_iff.2 (fun k => (hB.brownian k).cont)] with ω hω t ht
  let x (s : ℝ) := ∑ k, M.yvec k * M.Xtilde B ω s k
  have hx : Continuous x := by
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul ((hω k).comp continuous_real_toNNReal)))
  simpa [SystemSequence.Qstar, SystemSequence.Wstar, SystemSequence.Vstar, x, sub_eq_add_neg] using
    (hx.continuousWithinAt.sub (past_inf_right x hx t ht)).div_const (M.yvec 1)

private theorem ae_joint_positive_part {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ → ℝ) (hm : AEMeasurable (fun ω (t : ℝ≥0) => f ω t) P)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (f ω) (Ici t) t) :
    AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (f z.1 z.2))
      (P.prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let w := hm.mk (fun ω (t : ℝ≥0) => f ω t)
  have hw : Measurable w := hm.measurable_mk
  let ceilIdx (n : ℕ) (t : ℝ) := Nat.ceil (t * (2:ℝ)^n)
  let time (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (2 : ℝ≥0)^n
  let value (n : ℕ) (z : Ω × ℝ) := ENNReal.ofReal (w z.1 (time n (ceilIdx n z.2)))
  have hv (n : ℕ) : Measurable (value n) := by
    have hm₁ : Measurable (fun z : Ω × ℕ => w z.1 (time n z.2)) :=
      measurable_from_prod_countable_left (fun k => (measurable_pi_apply (time n k)).comp hw)
    have hm₂ : Measurable (ceilIdx n) := Nat.measurable_ceil.comp (measurable_id.mul_const _)
    exact ENNReal.measurable_ofReal.comp (hm₁.comp (measurable_fst.prodMk (hm₂.comp measurable_snd)))
  let G (z : Ω × ℝ) := liminf (fun n => value n z) atTop
  have hG : Measurable G := Measurable.liminf hv
  refine hG.aemeasurable.congr ?_
  have hA : ∀ᵐ z : Ω × ℝ ∂P.prod (volume.restrict (Ioi (0 : ℝ))),
      (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt (f z.1) (Ici t) t) ∧
        (fun t : ℝ≥0 => f z.1 t) = w z.1 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := P) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (hR.and hm.ae_eq_mk)
  have hT : ∀ᵐ z : Ω × ℝ ∂P.prod (volume.restrict (Ioi (0 : ℝ))), 0 ≤ z.2 := by
    apply (Measure.quasiMeasurePreserving_snd (μ := P) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
    exact (ae_restrict_mem measurableSet_Ioi).mono fun _ ht => ht.le
  filter_upwards [hA,hT] with z hz ht
  have heq (n : ℕ) : time n (ceilIdx n z.2) =
      (Nat.ceil ((z.2.toNNReal : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n := by
    simp [time,ceilIdx,Real.coe_toNNReal,ht]
  have hConv : Tendsto (fun n => (time n (ceilIdx n z.2) : ℝ)) atTop (𝓝 z.2) := by
    have h := (NNReal.continuous_coe.tendsto z.2.toNNReal).comp
      (AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto z.2.toNNReal)
    simpa only [Function.comp_def, Real.coe_toNNReal _ ht, heq] using h
  have hFrom : ∀ᶠ n in atTop, (time n (ceilIdx n z.2) : ℝ) ∈ Ici z.2 := by
    apply Eventually.of_forall
    intro n
    have h := AvramDividend.Classical.dyadic_ceiling_time_ge_nnreal z.2.toNNReal n
    have hr : (z.2.toNNReal : ℝ) ≤ (time n (ceilIdx n z.2) : ℝ) := by
      rw [heq]
      exact_mod_cast h
    exact mem_Ici.mpr (by simpa only [Real.coe_toNNReal _ ht] using hr)
  have hlim := (hz.1 z.2 ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hConv,hFrom⟩)
  have hl : Tendsto (fun n => value n z) atTop (𝓝 (ENNReal.ofReal (f z.1 z.2))) := by
    have hf := (ENNReal.continuous_ofReal.tendsto (f z.1 z.2)).comp hlim
    apply hf.congr
    intro n
    exact congrArg ENNReal.ofReal (congrFun hz.2 (time n (ceilIdx n z.2)))
  exact hl.liminf_eq

private theorem expected_positive_part_converges {Ω Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P : Measure Ω) (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P]
    (a : ℕ → Ω₁ → ℝ) (b : Ω₂ → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (ha : ∀ᶠ n in atTop, IdentDistrib (Y n) (a n) P P₁)
    (hb : IdentDistrib Z b P P₂)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (K : ℝ≥0∞) (hK : K < ⊤)
    (hmom : ∀ᶠ n in atTop, (∫⁻ ω, ENNReal.ofReal (a n ω)^2 ∂P₁) ≤ K) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (a n ω) ∂P₁) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (b ω) ∂P₂)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 ha
  let Y₀ (n : ℕ) := if h : N ≤ n then (hN n h).aemeasurable_fst.mk (Y n) else fun _ => 0
  let Z₀ := hb.aemeasurable_fst.mk Z
  let Y' (n : ℕ) (ω : Ω) := max 0 (Y₀ n ω)
  let Z' (ω : Ω) := max 0 (Z₀ ω)
  have hYm (n : ℕ) : Measurable (Y' n) := by
    apply Measurable.max measurable_const
    dsimp only [Y₀]
    split
    · exact AEMeasurable.measurable_mk _
    · exact measurable_const
  have hZm : Measurable Z' := measurable_const.max hb.aemeasurable_fst.measurable_mk
  have hYe (n : ℕ) : ∀ᵐ ω ∂P, N ≤ n → Y n ω = Y₀ n ω := by
    by_cases h : N ≤ n
    · filter_upwards [(hN n h).aemeasurable_fst.ae_eq_mk] with ω hω _
      simpa only [Y₀, dif_pos h] using hω
    · simp [h]
  have hConv : ∀ᵐ ω ∂P, Tendsto (fun n => Y' n ω) atTop (𝓝 (Z' ω)) := by
    filter_upwards [hconv, ae_all_iff.2 hYe,hb.aemeasurable_fst.ae_eq_mk] with ω hω hY hZ
    have hh := (tendsto_const_nhds (x := (0 : ℝ))).max hω
    have hz : max 0 (Z ω) = Z' ω := congrArg (max 0) hZ
    rw [hz] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    exact congrArg (max 0) (hY n hn)
  have hEq (n : ℕ) (hn : N ≤ n) (v : ℝ≥0∞ → ℝ≥0∞) (hv : Measurable v) :
      (∫⁻ ω, v (ENNReal.ofReal (Y' n ω)) ∂P) = ∫⁻ ω, v (ENNReal.ofReal (a n ω)) ∂P₁ := by
    calc
      _ = ∫⁻ ω, v (ENNReal.ofReal (Y n ω)) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hYe n] with ω hω
        simp [Y', ← hω hn, ENNReal.ofReal_max]
      _ = _ := ((hN n hn).comp (hv.comp ENNReal.measurable_ofReal)).lintegral_eq
  have hZE : (∫⁻ ω, ENNReal.ofReal (Z' ω) ∂P) = ∫⁻ ω, ENNReal.ofReal (b ω) ∂P₂ := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hb.aemeasurable_fst.ae_eq_mk] with ω hω
        simp [Z', Z₀, ← hω, ENNReal.ofReal_max]
      _ = _ := (hb.comp ENNReal.measurable_ofReal).lintegral_eq
  have hM : ∀ᶠ n in atTop, (∫⁻ ω, ENNReal.ofReal (Y' n ω) ^ (2:ℝ) ∂P) ≤ K := by
    filter_upwards [eventually_ge_atTop N,hmom] with n hn hh
    simpa only [ENNReal.rpow_two, hEq n hn (fun v => v^2) (measurable_id.pow_const 2)] using
      (show (∫⁻ ω, ENNReal.ofReal (Y' n ω) ^ 2 ∂P) ≤ K from by
        rw [hEq n hn (fun v => v^2) (measurable_id.pow_const 2)]; exact hh)
  obtain ⟨hZi, hc⟩ := ManyServerQED.Scheduling.nonnegative_cost_expectation_from_ae_limit_and_moment
    P Y' Z' hYm hZm (fun _ => ae_of_all _ fun _ => le_max_left _ _)
    (ae_of_all _ fun _ => le_max_left _ _) hConv 2 (by norm_num) K hK hM
  rw [ofReal_integral_eq_lintegral_ofReal hZi (ae_of_all _ fun _ => le_max_left _ _), hZE] at hc
  refine hc.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hEq n hn id measurable_id

private theorem exp_poly_lintegral_ne_top {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) (p : ℕ) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-γ*t) * (1+C*(1+t)^p))) ≠ ⊤ := by
  have h₁ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hγ) 0
  have h₂ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t) * t^p) (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p:ℝ)) (b := γ) (p := (1:ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) p; linarith) one_pos hγ
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul, mul_comm] using h
  have h₃ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t) * (1+C*(1+t)^p)) (Ioi (0:ℝ)) := by
    have h := h₁.add ((h₁.const_mul (C * 2^p)).add (h₂.const_mul (C * 2^p)))
    refine h.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hp : (1+t)^p ≤ 2^p + 2^p*t^p := by
      by_cases hsmall : t ≤ 1
      · exact (pow_le_pow_left₀ (by positivity) (by linarith) p).trans
          (le_add_of_nonneg_right (by positivity))
      · have hb : 1+t ≤ 2*t := by linarith
        exact ((pow_le_pow_left₀ (by positivity) hb p).trans_eq (mul_pow _ _ _)).trans
          (le_add_of_nonneg_left (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc := mul_le_mul_of_nonneg_left hp hC
    have he := mul_le_mul_of_nonneg_left (add_le_add_left hc 1) (Real.exp_nonneg (-γ*t))
    change Real.exp (-γ*t) * (1+C*(1+t)^p) ≤
      Real.exp (-γ*t) + (C * 2^p * Real.exp (-γ*t) + C * 2^p * (Real.exp (-γ*t) * t^p))
    calc
      _ = Real.exp (-γ*t) * (C*(1+t)^p + 1) := by ring
      _ ≤ Real.exp (-γ*t) * (C*(2^p+2^p*t^p) + 1) := he
      _ = _ := by ring
  have hNon : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun t => Real.exp (-γ*t) * (1+C*(1+t)^p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    show 0 ≤ Real.exp (-γ*t) * (1+C*(1+t)^p)
    positivity
  exact (hasFiniteIntegral_iff_ofReal hNon).1 h₃.hasFiniteIntegral |>.ne

set_option maxHeartbeats 1250000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ᶠ n in atTop, M.IsAdmissible n (T n))
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B)
    (hCouple : CouplingConverges M.P P'
      (fun n ω t => ![M.Qhat n (T n) ω t 0, M.Qhat n (T n) ω t 1,
        M.Ihat n (T n) ω t 0, M.Ihat n (T n) ω t 1])
      (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]))
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hMom : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
      (∫⁻ ω, (ENNReal.ofReal (∑ k, M.h k * M.Qhat n (T n) ω t k)) ^ 2 ∂M.P) ≤
        ENNReal.ofReal (C * (1 + t) ^ p)) :
    Tendsto (fun n => M.cost n (T n)) atTop (𝓝 (M.Jstar P' B)) ∧ M.Jstar P' B < ⊤ := by
  obtain ⟨Ωc, mΩc, Pc, Y, Z, hProb, hLaw, hLawZ, _, hConv⟩ := hCouple
  letI : IsProbabilityMeasure M.P := M.isProb
  letI : IsProbabilityMeasure P' := hB.isProb
  letI : IsProbabilityMeasure Pc := hProb
  let a (n : ℕ) (ω : Ω) (t : ℝ) := ∑ k, M.h k * M.Qhat n (T n) ω t k
  let b (ω : Ω') (t : ℝ) := ∑ k, M.h k * M.Qstar B ω t k
  let sumQ (q : Fin 4 → ℝ) := M.h 0 * q 0 + M.h 1 * q 1
  have hsumQ : Measurable sumQ := by
    exact ((measurable_pi_apply (0:Fin 4)).const_mul _).add
      ((measurable_pi_apply (1:Fin 4)).const_mul _)
  let liftQ (w : ℝ≥0 → Fin 4 → ℝ) (t : ℝ≥0) := sumQ (w t)
  have hlift : Measurable liftQ := measurable_pi_lambda _ fun t =>
    hsumQ.comp (measurable_pi_apply t)
  have hALaw : ∀ᶠ n in atTop, IdentDistrib (fun ω (t : ℝ≥0) => sumQ (Y n ω t))
      (fun ω (t : ℝ≥0) => a n ω t) Pc M.P := by
    filter_upwards [hLaw] with n hn
    simpa [liftQ, sumQ, a, Function.comp_def, Fin.sum_univ_two] using hn.comp hlift
  have hBLaw : IdentDistrib (fun ω (t : ℝ≥0) => sumQ (Z ω t))
      (fun ω (t : ℝ≥0) => b ω t) Pc P' := by
    simpa [liftQ, sumQ, b, Function.comp_def, Fin.sum_univ_two, SystemSequence.Qstar] using
      hLawZ.comp hlift
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (a n ω t) ∂M.P) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (b ω t) ∂P')) := by
    have hlaw : ∀ᶠ n in atTop, IdentDistrib (fun ω => sumQ (Y n ω t)) (fun ω => a n ω t) Pc M.P := by
      filter_upwards [hALaw] with n hn
      simpa [Function.comp_def, Real.coe_toNNReal _ ht] using hn.comp (measurable_pi_apply t.toNNReal)
    have hlawZ : IdentDistrib (fun ω => sumQ (Z ω t)) (fun ω => b ω t) Pc P' := by
      simpa [Function.comp_def, Real.coe_toNNReal _ ht] using hBLaw.comp (measurable_pi_apply t.toNNReal)
    have hcv : ∀ᵐ ω ∂Pc, Tendsto (fun n => sumQ (Y n ω t)) atTop (𝓝 (sumQ (Z ω t))) := by
      filter_upwards [hConv] with ω hω
      have hi (i : Fin 4) : Tendsto (fun n => Y n ω t i) atTop (𝓝 (Z ω t i)) := by
        apply Metric.tendsto_nhds.2
        intro ε hε
        filter_upwards [(hω t ht).eventually_lt_const (ENNReal.ofReal_pos.2 hε)] with n hn
        have hsum : |Y n ω t i - Z ω t i| ≤ ∑ j, |Y n ω t j - Z ω t j| :=
          Finset.single_le_sum (fun j _ => abs_nonneg (Y n ω t j - Z ω t j)) (Finset.mem_univ i)
        have hSup : ENNReal.ofReal (∑ j, |Y n ω t j - Z ω t j|) ≤ supDist (Y n ω) (Z ω) t :=
          le_iSup_of_le t (le_iSup_of_le ⟨ht,le_rfl⟩ le_rfl)
        rw [Real.dist_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).1
          ((ENNReal.ofReal_le_ofReal hsum).trans_lt (hSup.trans_lt hn))
      exact ((hi 0).const_mul _).add ((hi 1).const_mul _)
    exact expected_positive_part_converges Pc M.P P' (fun n ω => a n ω t) (fun ω => b ω t)
      (fun n ω => sumQ (Y n ω t)) (fun ω => sumQ (Z ω t)) hlaw hlawZ hcv _ ENNReal.ofReal_lt_top
      (hMom.mono fun _ hn => hn t ht)
  let ν := volume.restrict (Ioi (0:ℝ))
  let d (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t))
  let F (n : ℕ) (t : ℝ) := (∫⁻ ω, d t * ENNReal.ofReal (a n ω t) ∂M.P)
  let G (t : ℝ) := (∫⁻ ω, d t * ENNReal.ofReal (b ω t) ∂P')
  let D (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t) * (1+C*(1+t)^p))
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hJn : ∀ᶠ n in atTop, AEMeasurable (fun z : Ω × ℝ => d z.2 * ENNReal.ofReal (a n z.1 z.2))
      (M.P.prod ν) := by
    filter_upwards [hALaw, hT] with n nLaw hn
    refine (hd.comp measurable_snd).aemeasurable.mul
      (ae_joint_positive_part M.P (a n) nLaw.aemeasurable_snd (ae_of_all _ fun ω t ht => ?_))
    simpa only [a, Fin.sum_univ_two, Pi.add_def] using ((queue_right M n (T n) hn ω 0 t ht).const_mul (M.h 0)).add
      ((queue_right M n (T n) hn ω 1 t ht).const_mul (M.h 1))
  have hJL : AEMeasurable (fun z : Ω' × ℝ => d z.2 * ENNReal.ofReal (b z.1 z.2)) (P'.prod ν) := by
    refine (hd.comp measurable_snd).aemeasurable.mul
      (ae_joint_positive_part P' b hBLaw.aemeasurable_snd ?_)
    filter_upwards [qstar_right_ae M P' B hB] with ω hω t ht
    have he : b ω = fun t => M.h 1 * M.Qstar B ω t 1 := by
      funext v
      simp [b, Fin.sum_univ_two, SystemSequence.Qstar]
    rw [he]
    exact (hω t ht).const_mul (M.h 1)
  have hcn : ∀ᶠ n in atTop, M.cost n (T n) = ∫⁻ t, F n t ∂ν := by
    filter_upwards [hJn] with n hn
    have hr := lintegral_lintegral_swap (f := fun ω t => d t * ENNReal.ofReal (a n ω t)) hn
    simpa only [SystemSequence.cost, d, a, F, ν, ENNReal.ofReal_mul (Real.exp_nonneg _)] using hr
  have hcL : M.Jstar P' B = ∫⁻ t, G t ∂ν := by
    have hr := lintegral_lintegral_swap (f := fun ω t => d t * ENNReal.ofReal (b ω t)) hJL
    simpa only [SystemSequence.Jstar, d, b, G, ν, ENNReal.ofReal_mul (Real.exp_nonneg _)] using hr
  have hFG (t : ℝ) (ht : 0 ≤ t) : Tendsto (fun n => F n t) atTop (𝓝 (G t)) := by
    simpa only [F, G, lintegral_const_mul' (d t) _ ENNReal.ofReal_ne_top] using
      ENNReal.Tendsto.const_mul (a := d t) (hpoint t ht) (Or.inr ENNReal.ofReal_ne_top)
  have hDom : ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → F n t ≤ D t := by
    filter_upwards [hMom] with n hn t ht
    have hbas (x : ℝ) : ENNReal.ofReal x ≤ 1 + ENNReal.ofReal x ^ 2 := by
      by_cases hx : 0 ≤ x
      · have hh : x ≤ 1 + x^2 := by nlinarith [sq_nonneg (x-1)]
        have hh' := ENNReal.ofReal_le_ofReal hh
        simpa [ENNReal.ofReal_add zero_le_one (sq_nonneg x), ENNReal.ofReal_pow hx] using hh'
      · simp [ENNReal.ofReal_eq_zero.2 (le_of_not_ge hx)]
    have hInt : (∫⁻ ω, ENNReal.ofReal (a n ω t) ∂M.P) ≤ 1 + ENNReal.ofReal (C * (1+t)^p) := by
      calc
        _ ≤ ∫⁻ ω, 1 + ENNReal.ofReal (a n ω t)^2 ∂M.P := lintegral_mono (fun ω => hbas _)
        _ = 1 + (∫⁻ ω, ENNReal.ofReal (a n ω t)^2 ∂M.P) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        _ ≤ _ := add_le_add_right (hn t ht) _
    change (∫⁻ ω, d t * ENNReal.ofReal (a n ω t) ∂M.P) ≤ D t
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpoly : 0 ≤ C * (1+t)^p := by positivity
    simpa only [D, d, ENNReal.ofReal_mul (Real.exp_nonneg _),
      ENNReal.ofReal_add zero_le_one hpoly, ENNReal.ofReal_one] using (show d t * (∫⁻ ω, ENNReal.ofReal (a n ω t) ∂M.P) ≤
        d t * (1 + ENNReal.ofReal (C * (1+t)^p)) from by gcongr)
  have hDom' : ∀ᶠ n in atTop, ∀ᵐ t ∂ν, F n t ≤ D t := hDom.mono (fun n hn => by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hn t ht.le)
  have hLim : ∀ᵐ t ∂ν, Tendsto (fun n => F n t) atTop (𝓝 (G t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hFG t ht.le
  have hFin : (∫⁻ t, D t ∂ν) ≠ ⊤ := exp_poly_lintegral_ne_top M.gamma_pos hC p
  have hDCT := tendsto_lintegral_filter_of_dominated_convergence' D
    (hJn.mono fun _ hn => hn.lintegral_prod_left') hDom' hFin hLim
  refine ⟨?_, ?_⟩
  · rw [hcL]
    exact hDCT.congr' (hcn.mono fun _ hn => hn.symm)
  · rw [hcL]
    have hG : ∀ᵐ t ∂ν, G t ≤ D t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact le_of_tendsto (hFG t ht.le) (hDom.mono fun _ hn => hn t ht.le)
    exact (lintegral_mono_ae hG).trans_lt hFin.lt_top
