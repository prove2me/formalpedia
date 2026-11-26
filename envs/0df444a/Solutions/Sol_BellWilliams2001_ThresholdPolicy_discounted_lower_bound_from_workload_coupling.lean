-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.discounted_lower_bound_from_workload_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:47:28.544594+00:00
-- url     : https://prove2.me/submissions/590cc82a-6ab1-4d79-8231-90f80f20a969

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_cost_lower_bound_path
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_balance
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_discounted_cost_aemeasurable
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_past_infimum_from_dyadic_grid
import Definitions.Def_BellWilliams2001_ThresholdPolicy_BrownianControl

open BellWilliams2001.ThresholdPolicy
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

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

private noncomputable def grid (t : ℝ≥0) (p : ℕ × ℕ) : ℝ≥0 :=
  ⟨min (t:ℝ) ((p.2 : ℝ) / (2 : ℝ) ^ p.1), le_min t.2 (by positivity)⟩

private noncomputable def reflectionObs (t : ℝ≥0) (κ : ℝ)
    (f : ℝ≥0 → Fin 1 → ℝ) : ℝ≥0∞ :=
  ⨆ p : ℕ × ℕ, ENNReal.ofReal (κ * (f t 0 - f (grid t p) 0))

private theorem measurable_reflectionObs (t : ℝ≥0) (κ : ℝ) :
    Measurable (reflectionObs t κ) := by
  refine Measurable.iSup (fun p => ?_)
  have hval (s : ℝ≥0) : Measurable (fun f : ℝ≥0 → Fin 1 → ℝ => f s 0) :=
    (measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply s)
  simpa only [Pi.sub_def] using (((hval t).sub (hval (grid t p))).const_mul κ).ennreal_ofReal


private theorem cost_coefficient_limit {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n => min (M.h 0) (M.h 1 / M.poolingWeight (φ n))) atTop
      (𝓝 (M.h 1 / M.yvec 1)) := by
  have hm := (M.a31_iv 1).div (M.a31_iv 2) (M.mu_pos 2).ne'
  have hy : 0 < M.mu 1 / M.mu 2 := div_pos (M.mu_pos 1) (M.mu_pos 2)
  have h := (tendsto_const_nhds (x := M.h 0)).min ((tendsto_const_nhds (x := M.h 1)).div (hm.comp hφ) hy.ne')
  have hLe : M.h 1 / (M.mu 1 / M.mu 2) ≤ M.h 0 := by
    rw [div_div_eq_mul_div, div_le_iff₀ (M.mu_pos 1)]
    exact M.a32
  simpa only [SystemSequence.poolingWeight, SystemSequence.yvec, show (1:Fin 2) ≠ 0 by decide,
    if_false, min_eq_right hLe,Pi.div_def,Function.comp_def] using h

private theorem workload_input_bounded_below {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T) (ω : Ω)
    (t : ℝ) (ht : 0 ≤ t) :
    BddBelow (range (fun s : Icc (0:ℝ) t => M.workloadInput n T ω s)) := by
  let v (s : ℝ) := M.muR n 0 * M.Ihat n T ω s 0 + M.muR n 1 * M.Ihat n T ω s 1
  have hr : 0 < M.r n := zero_lt_one.trans_le (M.r_ge n)
  refine ⟨-v t, fun _ ⟨s,hs⟩ => hs ▸ ?_⟩
  have hs0 : 0 ≤ M.r n^2 * s := mul_nonneg (sq_nonneg _) s.2.1
  have ht0 : 0 ≤ M.r n^2 * t := mul_nonneg (sq_nonneg _) ht
  have hst : M.r n^2 * s ≤ M.r n^2 * t := mul_le_mul_of_nonneg_left s.2.2 (sq_nonneg _)
  have hI (k : Fin 2) : M.Ihat n T ω s k ≤ M.Ihat n T ω t k :=
    div_le_div_of_nonneg_right (hT.idle_mono ω k hs0 ht0 hst) hr.le
  have hv : v s ≤ v t := add_le_add (mul_le_mul_of_nonneg_left (hI 0) (M.muR_pos n 0).le)
    (mul_le_mul_of_nonneg_left (hI 1) (M.muR_pos n 1).le)
  have hq (k : Fin 2) : 0 ≤ M.Qhat n T ω s k :=
    div_nonneg (hT.queue_nonneg ω k _ hs0) hr.le
  have hw : 0 ≤ M.workload n T ω s :=
    add_nonneg (hq 0) (mul_nonneg (div_nonneg (M.muR_pos n 1).le (M.muR_pos n 2).le) (hq 1))
  rw [workload_balance,SystemSequence.serverTwoInput] at hw
  dsimp only [v] at hv ⊢
  linarith

private theorem point_of_uoc (U : ℕ → ℝ → Fin 1 → ℝ) (V : ℝ → Fin 1 → ℝ)
    (h : ∀ t : ℝ, 0 ≤ t → Tendsto (fun n => supDist (U n) V t) atTop (𝓝 0))
    (t : ℝ≥0) :
    Tendsto (fun n => U n t 0) atTop (𝓝 (V t 0)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(h t t.2).eventually_lt_const (ENNReal.ofReal_pos.2 hε)] with n hn
  have hSup : ENNReal.ofReal |U n t 0 - V t 0| ≤ supDist (U n) V t := by
    apply le_iSup_of_le (t : ℝ)
    apply le_iSup_of_le (show (t:ℝ) ∈ Icc (0:ℝ) (t:ℝ) from ⟨t.2,le_rfl⟩)
    simp
  rw [Real.dist_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hSup.trans_lt hn)

set_option maxHeartbeats 1850000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ)
    (hB : IsBrownianPair P' B)
    (hCouple : CouplingConverges M.P P'
      (fun n ω t => ![M.workloadInput (φ n) (T (φ n)) ω t])
      (fun ω t => ![∑ k, M.yvec k * M.Xtilde B ω t k])) :
    M.Jstar P' B ≤ liminf (fun n => M.cost (φ n) (T (φ n))) atTop := by
  classical
  obtain ⟨Ωc, mΩc, Pc, Y, Z, hProb, hLaw, hLawZ, _, hConv⟩ := hCouple
  letI : IsProbabilityMeasure M.P := M.isProb
  letI : IsProbabilityMeasure P' := hB.isProb
  letI : IsProbabilityMeasure Pc := hProb
  let κ (n : ℕ) := min (M.h 0) (M.h 1 / M.poolingWeight (φ n))
  let κlim := M.h 1 / M.yvec 1
  let x (n : ℕ) (ω : Ω) := M.workloadInput (φ n) (T (φ n)) ω
  let z (ω : Ω') (s : ℝ) := ∑ k, M.yvec k * M.Xtilde B ω s k
  let a (n : ℕ) (ω : Ω) (s : ℝ) := ∑ k, M.h k * M.Qhat (φ n) (T (φ n)) ω s k
  let b (ω : Ω') (s : ℝ) := ∑ k, M.h k * M.Qstar B ω s k
  have hκ (n : ℕ) : 0 ≤ κ n := le_min (M.h_pos 0).le (div_nonneg (M.h_pos 1).le
    (div_nonneg (M.muR_pos (φ n) 1).le (M.muR_pos (φ n) 2).le))
  have hκL : 0 ≤ κlim := div_nonneg (M.h_pos 1).le (div_nonneg (M.mu_pos 1).le (M.mu_pos 2).le)
  have hκconv : Tendsto κ atTop (𝓝 κlim) := cost_coefficient_limit M φ hφ
  have hx (n : ℕ) (ω : Ω) (t : ℝ≥0) :
      reflectionObs t (κ n) (fun s => ![x n ω s]) ≤ ENNReal.ofReal (a n ω t) := by
    refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
    let u : Icc (0:ℝ) (t:ℝ) := ⟨grid t p, (grid t p).2, by exact min_le_left _ _⟩
    letI : Nonempty (Icc (0:ℝ) (t:ℝ)) := ⟨⟨0,le_rfl,t.2⟩⟩
    have hbd := workload_input_bounded_below M (φ n) (T (φ n)) (hT (φ n)) ω t t.2
    have hi := ciInf_le hbd u
    have h := workload_cost_lower_bound_path M (φ n) (T (φ n)) (hT (φ n)) ω t t.2 hbd
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hi _) (hκ n)).trans h
  have hzc : ∀ᵐ ω ∂P', Continuous (z ω) := by
    filter_upwards [ae_all_iff.2 (fun k => (hB.brownian k).cont)] with ω hω
    apply continuous_finsetSum
    intro k _
    exact continuous_const.mul ((continuous_const.mul continuous_id).add
      (continuous_const.mul ((hω k).comp continuous_real_toNNReal)))
  have hz : ∀ᵐ ω ∂P', ∀ t : ℝ≥0,
      reflectionObs t κlim (fun s => ![z ω s]) = ENNReal.ofReal (b ω t) := by
    filter_upwards [hzc] with ω hω t
    let g (s : ℝ) := κlim * z ω s
    have hg : Continuous g := continuous_const.mul hω
    have hbdd : BddBelow (range (fun s : Icc (0:ℝ) (t:ℝ) => g s)) := by
      rw [← Set.image_eq_range]
      exact (isCompact_Icc.image hg).bddBelow
    letI : Nonempty (Icc (0:ℝ) (t:ℝ)) := ⟨⟨0,le_rfl,t.2⟩⟩
    have infMul : (⨅ s : Icc (0:ℝ) (t:ℝ), g s) =
        κlim * ⨅ s : Icc (0:ℝ) (t:ℝ), z ω s := by
      simp only [g]
      exact (Real.mul_iInf_of_nonneg hκL _).symm
    have hr := past_infimum_from_dyadic_grid g t (fun _ _ => hg.continuousWithinAt) hbdd
    have hR : reflectionObs t κlim (fun s => ![z ω s]) = ENNReal.ofReal (g t -
        ⨅ s : Icc (0:ℝ) (t:ℝ), g s) := by
      change (⨆ p : ℕ × ℕ, ENNReal.ofReal (κlim * (z ω t -
        z ω (min (t:ℝ) ((p.2:ℝ) / (2:ℝ)^p.1))))) = _
      simpa [g, mul_sub] using hr.symm
    rw [hR,infMul]
    congr 1
    simp only [b,g,z,Fin.sum_univ_two,SystemSequence.Qstar,if_true,show (1:Fin 2) ≠ 0 by decide,
      if_false,mul_zero,zero_add,SystemSequence.Wstar,SystemSequence.Vstar,κlim]
    ring
  have hBLaw : AEMeasurable (fun ω (t : ℝ≥0) => b ω t) P' := by
    let f (x : ℝ≥0 → Fin 1 → ℝ) (t : ℝ≥0) := (reflectionObs t κlim x).toReal
    have hm : Measurable f := measurable_pi_lambda _ fun t =>
      ENNReal.measurable_toReal.comp (measurable_reflectionObs t κlim)
    refine (hm.comp_aemeasurable hLawZ.aemeasurable_snd).congr ?_
    filter_upwards [hz,hzc] with ω hw hω
    funext t
    letI : Nonempty (Icc (0:ℝ) (t:ℝ)) := ⟨⟨0,le_rfl,t.2⟩⟩
    have hbd : BddBelow (range (fun s : Icc (0:ℝ) (t:ℝ) => z ω s)) := by
      rw [←Set.image_eq_range]
      exact (isCompact_Icc.image hω).bddBelow
    have hi := ciInf_le hbd (⟨t,t.2,le_rfl⟩ : Icc (0:ℝ) (t:ℝ))
    have hNN : 0 ≤ κlim * (z ω t - ⨅ s : Icc (0:ℝ) (t:ℝ), z ω s) :=
      mul_nonneg hκL (sub_nonneg.mpr hi)
    have hBnon : 0 ≤ b ω t := by
      convert hNN using 1
      simp only [κlim,b,z,Fin.sum_univ_two,SystemSequence.Qstar,if_true,show (1:Fin 2) ≠ 0 by decide,
        if_false,mul_zero,zero_add,SystemSequence.Wstar,SystemSequence.Vstar]
      ring
    change (reflectionObs t κlim (fun s => ![z ω s])).toReal = b ω t
    rw [hw t, ENNReal.toReal_ofReal hBnon]
  let ν := volume.restrict (Ioi (0:ℝ))
  let d (s : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*s))
  let F (n : ℕ) (s : ℝ) := ∫⁻ ω, d s * ENNReal.ofReal (a n ω s) ∂M.P
  let G (s : ℝ) := ∫⁻ ω, d s * ENNReal.ofReal (b ω s) ∂P'
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hJn (n : ℕ) : AEMeasurable (fun w : Ω × ℝ => d w.2 * ENNReal.ofReal (a n w.1 w.2)) (M.P.prod ν) := by
    have hm := (admissible_discounted_cost_aemeasurable M (φ n) (T (φ n)) (hT (φ n))).1
    simpa only [d,a,ν,Function.uncurry_def,ENNReal.ofReal_mul (Real.exp_nonneg _)] using hm
  have hJ : AEMeasurable (fun w : Ω' × ℝ => d w.2 * ENNReal.ofReal (b w.1 w.2)) (P'.prod ν) := by
    refine (hd.comp measurable_snd).aemeasurable.mul (ae_joint_positive_part P' b hBLaw ?_)
    filter_upwards [qstar_right_ae M P' B hB] with ω hω t ht
    have he : b ω = fun s => M.h 1 * M.Qstar B ω s 1 := by
      funext s
      simp [b,Fin.sum_univ_two,SystemSequence.Qstar]
    rw [he]
    exact (hω t ht).const_mul (M.h 1)
  have hCn (n : ℕ) : M.cost (φ n) (T (φ n)) = ∫⁻ s, F n s ∂ν := by
    simpa only [SystemSequence.cost,ν,d,a,F,ENNReal.ofReal_mul (Real.exp_nonneg _)] using
      (lintegral_lintegral_swap (f := fun ω s => d s * ENNReal.ofReal (a n ω s)) (hJn n))
  have hC : M.Jstar P' B = ∫⁻ s, G s ∂ν := by
    simpa only [SystemSequence.Jstar,ν,d,b,G,ENNReal.ofReal_mul (Real.exp_nonneg _)] using
      (lintegral_lintegral_swap (f := fun ω s => d s * ENNReal.ofReal (b ω s)) hJ)
  have hPoint (t : ℝ≥0) : G t ≤ liminf (fun n => F n t) atTop := by
    let H (n : ℕ) (ω : Ωc) := d t * reflectionObs t (κ n) (fun s => Y n ω s)
    let K (ω : Ωc) := d t * reflectionObs t κlim (fun s => Z ω s)
    have hH : ∀ᶠ n in atTop, AEMeasurable (H n) Pc := by
      filter_upwards [hLaw] with n hn
      exact ((measurable_reflectionObs t (κ n)).comp_aemeasurable hn.aemeasurable_fst).const_mul _
    let W (n : ℕ) := if AEMeasurable (H n) Pc then H n else (fun _ => 0)
    have hW (n : ℕ) : AEMeasurable (W n) Pc := by
      dsimp [W]
      split
      · assumption
      · exact aemeasurable_const
    have hEq : W =ᶠ[atTop] H := hH.mono fun n hn => if_pos hn
    have hFatou : (∫⁻ ω, K ω ∂Pc) ≤ liminf (fun n => ∫⁻ ω, H n ω ∂Pc) atTop := by
      calc
        _ ≤ ∫⁻ ω, liminf (fun n => W n ω) atTop ∂Pc := by
          refine lintegral_mono_ae ?_
          filter_upwards [hConv] with ω hω
          rw [liminf_congr (hEq.mono fun n hn => congrFun hn ω)]
          have hVal (s : ℝ≥0) := point_of_uoc (fun n => Y n ω) (Z ω) hω s
          have hd' : d t ≠ ⊤ := ENNReal.ofReal_ne_top
          dsimp only [K,reflectionObs]
          rw [ENNReal.mul_iSup]
          refine iSup_le fun p => ?_
          have hh := hκconv.mul ((hVal t).sub (hVal (grid t p)))
          have hh' := (ENNReal.continuous_ofReal.tendsto _).comp hh
          have hm := ENNReal.Tendsto.const_mul (a := d t) hh' (Or.inr hd')
          rw [← hm.liminf_eq]
          exact liminf_le_liminf (Eventually.of_forall fun n => by
            exact mul_le_mul' (le_refl (d t)) (le_iSup (fun q : ℕ × ℕ => ENNReal.ofReal
              (κ n * (Y n ω t 0 - Y n ω (grid t q) 0))) p))
        _ ≤ liminf (fun n => ∫⁻ ω, W n ω ∂Pc) atTop := lintegral_liminf_le' hW
        _ = _ := liminf_congr (hEq.mono fun n hn => congrArg (fun f => ∫⁻ ω, f ω ∂Pc) hn)
    have hGlaw : (∫⁻ ω, K ω ∂Pc) = G t := by
      have hl := (hLawZ.comp (measurable_reflectionObs t κlim)).comp (measurable_const_mul (d t))
      calc
        _ = ∫⁻ ω, d t * reflectionObs t κlim (fun s => ![z ω s]) ∂P' := hl.lintegral_eq
        _ = _ := lintegral_congr_ae (hz.mono fun _ hh => congrArg (d t * ·) (hh t))
    have hNlaw : ∀ᶠ n in atTop, (∫⁻ ω, H n ω ∂Pc) ≤ F n t := by
      filter_upwards [hLaw] with n hn
      have hl := (hn.comp (measurable_reflectionObs t (κ n))).comp (measurable_const_mul (d t))
      calc
        _ = ∫⁻ ω, d t * reflectionObs t (κ n) (fun s => ![x n ω s]) ∂M.P := hl.lintegral_eq
        _ ≤ _ := lintegral_mono fun ω => mul_le_mul' (le_refl (d t)) (hx n ω t)
    rw [← hGlaw]
    exact hFatou.trans (liminf_le_liminf hNlaw)
  rw [hC]
  simp_rw [hCn]
  calc
    _ ≤ ∫⁻ s, liminf (fun n => F n s) atTop ∂ν := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact_mod_cast hPoint (⟨s,hs.le⟩ : ℝ≥0)
    _ ≤ _ := lintegral_liminf_le' (fun n => (hJn n).lintegral_prod_left')
