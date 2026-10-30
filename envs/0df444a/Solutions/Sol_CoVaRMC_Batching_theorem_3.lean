-- Prove2me | solution 1 for CoVaRMC.Batching.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T22:38:58.825991+00:00
-- url     : https://prove2.me/submissions/f1e3a8ff-f441-4153-8962-cfb7024049fd

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Theorems.Thm_CoVaRMC_Batching_lemma_3
import Theorems.Thm_CoVaRMC_Batching_cond_density
import Theorems.Thm_CoVaRMC_Batching_eq_30
import Theorems.Thm_CoVaRMC_Batching_eq_31
import Theorems.Thm_CoVaRMC_Batching_eq_32

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRThm3Aux



lemma measurableSet_sort_eq {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {ω | Tuple.sort (fun j => X j ω) = σ} := by
  have : {ω | Tuple.sort (fun j => X j ω) = σ} =
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i ≤ j → X (σ i) ω ≤ X (σ j) ω}) ∩
      (⋂ i : Fin N, ⋂ j : Fin N, {ω | i < j → X (σ i) ω = X (σ j) ω → σ i < σ j}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simp only [hij, true_implies]
      exact measurableSet_le (hX _) (hX _)
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hs : σ i < σ j
      · simp [hs]
      · simp only [hij, hs, true_implies, imp_false]
        exact (measurableSet_eq_fun (hX _) (hX _)).compl
    · simp [hij]

lemma measurable_induced {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X A : Fin N → Ω → ℝ)
    (hX : ∀ j, Measurable (X j)) (hA : ∀ j, Measurable (A j)) (r : Fin N) :
    Measurable (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) := by
  have heq : (fun ω => A (Tuple.sort (fun j => X j ω) r) ω) = fun ω =>
      ∑ σ : Equiv.Perm (Fin N),
        Set.indicator {ω | Tuple.sort (fun j => X j ω) = σ} (A (σ r)) ω := by
    funext ω
    rw [Finset.sum_eq_single (Tuple.sort (fun j => X j ω))]
    · simp
    · intro σ _ hσ
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_ofPred_eq]
      exact fun h => hσ h.symm
    · simp
  rw [heq]
  exact Finset.measurable_sum _ fun σ _ =>
    (hA _).indicator (measurableSet_sort_eq X hX σ)

open CoVaRMC.Batching

lemma measurable_Yhat {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α : ℝ) (m i : ℕ) :
    Measurable (fun ω => Yhat S α m i ω) := by
  unfold Yhat
  by_cases hm : 0 < m
  · simp only [dif_pos hm, ImpactInvesting.Portfolio.inducedOrderStat]
    exact measurable_induced (fun j : Fin m => fun ω => (S (i, j) ω).1)
      (fun j : Fin m => fun ω => (S (i, j) ω).2) (fun j => (hSm _).fst) (fun j => (hSm _).snd) _
  · simp only [dif_neg hm]; exact measurable_const

lemma measurable_YBE {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α β : ℝ) (k m : ℕ) :
    Measurable (fun ω => YBE S α β k m ω) := by
  unfold YBE
  by_cases hk : 0 < k
  · simp only [dif_pos hk, ImpactInvesting.Portfolio.orderStat]
    exact measurable_induced (fun i : Fin k => fun ω => Yhat S α m i ω)
      (fun i : Fin k => fun ω => Yhat S α m i ω) (fun i => measurable_Yhat S hSm α m i)
      (fun i => measurable_Yhat S hSm α m i) _
  · simp only [dif_neg hk]; exact measurable_const

lemma measurable_FkHat {Ω : Type*} [MeasurableSpace Ω] (S : ℕ × ℕ → Ω → ℝ × ℝ)
    (hSm : ∀ p, Measurable (S p)) (α : ℝ) (k m : ℕ) (y : ℝ) :
    Measurable (fun ω => FkHat S α k m y ω) := by
  unfold FkHat empCDF
  refine measurable_const.mul ?_
  have : (fun ω => (((Finset.univ.filter fun i : Fin k => Yhat S α m i ω ≤ y).card : ℕ) : ℝ)) =
      fun ω => ∑ i : Fin k, Set.indicator {ω | Yhat S α m i ω ≤ y} (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : Yhat S α m i ω ≤ y <;> simp [h]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator (measurableSet_le (measurable_Yhat S hSm α m i) measurable_const)

/-- Standard normal cdf is continuous. -/
lemma continuous_Phi : Continuous (cdf (gaussianReal 0 1)) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro x
  have hm : Monotone (cdf (gaussianReal 0 1)) := monotone_cdf _
  rw [hm.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h1 := (cdf (gaussianReal 0 1)).measure_singleton x
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have h2 := hm.leftLim_le (le_refl x)
  linarith

lemma Phi_neg (a : ℝ) : cdf (gaussianReal 0 1) (-a) = 1 - cdf (gaussianReal 0 1) a := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [cdf_eq_real, cdf_eq_real]
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have : (gaussianReal 0 1).real (Set.Iic (-a)) = (gaussianReal 0 1).real (Set.Ici a) := by
    conv_lhs => rw [← hmap]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x; simp
  rw [this, ← Set.Ioi_union_left, measureReal_union (by simp) (measurableSet_singleton a),
    measureReal_def (s := {a}), measure_singleton, ENNReal.toReal_zero, add_zero, ← Set.compl_Iic,
    measureReal_compl measurableSet_Iic]
  simp


lemma tendstoInDist_of_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ ν, Measurable (X ν)) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : ∀ s, Tendsto (fun ν => P.real {ω | X ν ω ≤ s}) atTop (𝓝 (cdf μ s))) :
    TendstoInDistribution X atTop id (fun _ => P) μ := by
  refine ⟨fun ν => (hX ν).aemeasurable, aemeasurable_id, ?_⟩
  apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ))
  · rintro s ⟨a, b, -, rfl⟩; exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    refine ⟨Set.Ioc (x - ε / 2) (x + ε / 2), ⟨x - ε / 2, x + ε / 2, by simp only [id]; linarith, rfl⟩,
      ?_, ?_⟩
    · exact mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) Set.Ioo_subset_Ioc_self
    · intro y hy
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
  · rintro s ⟨a, b, hab, rfl⟩
    simp only [id] at hab ⊢
    rw [← NNReal.tendsto_coe]
    show Tendsto (fun ν => ((((P.map (X ν)) (Set.Ioc a b)).toNNReal : NNReal) : ℝ)) atTop
      (𝓝 ((((μ.map id) (Set.Ioc a b)).toNNReal : NNReal) : ℝ))
    simp only [ENNReal.coe_toNNReal_eq_toReal, ← measureReal_def, Measure.map_id]
    have hdiff : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext x; simp [and_comm]
    have hlim : μ.real (Set.Ioc a b) = cdf μ b - cdf μ a := by
      rw [hdiff, measureReal_sdiff (Set.Iic_subset_Iic.mpr hab.le) measurableSet_Iic, cdf_eq_real,
        cdf_eq_real]
    rw [hlim]
    have heq : ∀ ν, (P.map (X ν)).real (Set.Ioc a b) =
        P.real {ω | X ν ω ≤ b} - P.real {ω | X ν ω ≤ a} := by
      intro ν
      rw [map_measureReal_apply (hX ν) measurableSet_Ioc, hdiff, Set.preimage_sdiff,
        measureReal_sdiff (Set.preimage_mono (Set.Iic_subset_Iic.mpr hab.le))
          (measurableSet_Iic.preimage (hX ν))]
      rfl
    simp_rw [heq]
    exact (h b).sub (h a)

lemma opr_of_eventually {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ) (hU : ∀ ν, Measurable (U ν))
    (h : ∀ ε > 0, ∃ C > 0, ∀ᶠ ν in atTop, P {ω | C < |U ν ω|} ≤ ENNReal.ofReal ε) :
    ∀ ε > 0, ∃ C > 0, ∀ ν, P {ω | C < |U ν ω|} ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C0, hC0, hev⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hind : ∀ ν, ∃ C > 0, P {ω | C < |U ν ω|} ≤ ENNReal.ofReal ε := by
    intro ν
    have ht : Tendsto (fun n : ℕ => P {ω | (n : ℝ) < |U ν ω|}) atTop
        (𝓝 (P (⋂ n : ℕ, {ω | (n : ℝ) < |U ν ω|}))) := by
      apply tendsto_measure_iInter_atTop
      · exact fun n => (measurableSet_lt measurable_const (hU ν).abs).nullMeasurableSet
      · intro n n' hnn' ω hω
        simp only [Set.mem_ofPred_eq] at hω ⊢
        exact lt_of_le_of_lt (by exact_mod_cast hnn') hω
      · exact ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ n : ℕ, {ω | (n : ℝ) < |U ν ω|}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall,
        not_lt]
      obtain ⟨n, hn⟩ := exists_nat_ge |U ν ω|
      exact ⟨n, hn⟩
    rw [hempty, measure_empty] at ht
    obtain ⟨n0, hn0⟩ := eventually_atTop.mp
      (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε)))
    refine ⟨(n0 + 1 : ℕ), by positivity, (hn0 (n0 + 1) (by omega)).le⟩
  choose Cf hCf hCfb using hind
  refine ⟨C0 + ∑ ν ∈ Finset.range N, Cf ν,
    add_pos_of_pos_of_nonneg hC0 (Finset.sum_nonneg fun i _ => (hCf i).le), ?_⟩
  intro ν
  by_cases hν : N ≤ ν
  · refine le_trans (measure_mono ?_) (hN ν hν)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : 0 ≤ ∑ ν ∈ Finset.range N, Cf ν := Finset.sum_nonneg fun i _ => (hCf i).le
    linarith
  · refine le_trans (measure_mono ?_) (hCfb ν)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have : Cf ν ≤ ∑ ν ∈ Finset.range N, Cf ν :=
      Finset.single_le_sum (fun i _ => (hCf i).le) (Finset.mem_range.mpr (by omega))
    linarith

lemma rate_identity (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    √(k : ℝ) * ((k * m : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) = (√(k : ℝ) / m) ^ (1 / 3 : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  rw [Real.mul_rpow hk'.le hm'.le, Real.div_rpow (Real.sqrt_nonneg _) hm'.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hk'.le, Real.rpow_neg hm'.le, Real.rpow_neg hk'.le,
    show (1 / 2 : ℝ) * (1 / 3) = 1 / 2 - 1 / 3 by norm_num, Real.rpow_sub hk']
  field_simp

open CoVaRMC.Batching in
/-- The expansion after (32) with a constant `K` that does not depend on `t`. -/
lemma eq32_uniform (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      ∀ᶠ ν in atTop, |cmk P S α β c (Aconst D β v c) t (k ν) (m ν) + t - g ν| ≤
        K * √(k ν : ℝ) / m ν := by
  have hA1' := hA1
  obtain ⟨h𝒳o, hv𝒳, h𝒴o, hc𝒴, -, -, -, -, -⟩ := hA1'
  have hcd := CoVaRMC.Batching.cond_density D Fc v c 𝒳 𝒴 hFc hA1 v hv𝒳 c hc𝒴
  set f := D.condDensity c v with hfdef
  set A := Aconst D β v c with hAdef
  set σ0 := √(β * (1 - β)) with hσ0
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.mpr (mul_pos hβ.1 (by linarith [hβ.2]))
  have hApos : 0 < A := by
    simp only [hAdef, Aconst]
    exact div_pos hσ0pos hcd.2
  have hAf : A * f = σ0 := by
    simp only [hAdef, Aconst, ← hfdef, ← hσ0]; field_simp [hcd.2.ne']
  obtain ⟨C, hC⟩ := CoVaRMC.Batching.lemma_3 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
      P S hSm hSi hSl
  refine ⟨2 * |C| / σ0, by positivity, fun t => ?_⟩
  obtain ⟨-, -, hσlim⟩ := CoVaRMC.Batching.eq_30 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
    P S hSm hSi hSl k m hk0 hm0 hk hm t
  set σ : ℕ → ℝ := fun ν => sigmaHat P S α (m ν) (yk c A t (k ν)) with hσdef
  set F : ℕ → ℝ := fun ν => Fc (yk c A t (k ν)) v with hFdef
  set p : ℕ → ℝ := fun ν => pHat P S α (m ν) (yk c A t (k ν)) with hpdef
  have hsk : Tendsto (fun ν => √(k ν : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  have hskpos : ∀ ν, 0 < √(k ν : ℝ) := fun ν => Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)
  have hlin : Tendsto (fun ν => √(k ν : ℝ) * (F ν - β)) atTop (𝓝 (t * A * f)) := by
    by_cases ht : t = 0
    · simp only [hFdef, yk, ht, zero_mul, zero_div, add_zero, hc, sub_self, mul_zero]
      exact tendsto_const_nhds
    set h : ℕ → ℝ := fun ν => t * A / √(k ν : ℝ) with hhdef
    have hh0 : Tendsto h atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact hsk.const_div_atTop _
      · exact Eventually.of_forall fun ν => div_ne_zero (mul_ne_zero ht hApos.ne') (hskpos ν).ne'
    have hslope := (hasDerivAt_iff_tendsto_slope_zero.mp hcd.1).comp hh0
    have heq : ∀ ν, √(k ν : ℝ) * (F ν - β) =
        (t * A) * ((h ν)⁻¹ • (Fc (c + h ν) v - Fc c v)) := by
      intro ν
      simp only [hFdef, hhdef, yk, hc, smul_eq_mul]
      field_simp [(hskpos ν).ne', ht, hApos.ne']
    simp_rw [heq]
    exact hslope.const_mul _
  set g : ℕ → ℝ := fun ν => √(k ν : ℝ) / σ ν * (β - F ν) + t with hgdef
  refine ⟨g, ?_, ?_⟩
  · have : Tendsto g atTop (𝓝 (-(1 / σ0) * (t * A * f) + t)) := by
      have h1 : Tendsto (fun ν => -(1 / σ ν) * (√(k ν : ℝ) * (F ν - β)) + t) atTop
          (𝓝 (-(1 / σ0) * (t * A * f) + t)) :=
        (((tendsto_const_nhds.div hσlim hσ0pos.ne').neg).mul hlin).add tendsto_const_nhds
      refine h1.congr (fun ν => ?_)
      simp only [hgdef]; ring
    have h0 : -(1 / σ0) * (t * A * f) + t = 0 := by
      rw [mul_assoc t, hAf]; field_simp; ring
    rwa [h0] at this
  · have hyk : Tendsto (fun ν => yk c A t (k ν)) atTop (𝓝 c) := by
      simp only [yk]
      simpa using (hsk.const_div_atTop (t * A)).const_add c
    have hev1 : ∀ᶠ ν in atTop, ∀ y ∈ 𝒴, |pHat P S α (m ν) y - Fc y v| ≤ C / m ν :=
      hm.eventually hC
    have hev2 : ∀ᶠ ν in atTop, yk c A t (k ν) ∈ 𝒴 := hyk.eventually (h𝒴o.mem_nhds hc𝒴)
    have hev3 : ∀ᶠ ν in atTop, σ0 / 2 < σ ν :=
      hσlim.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev1, hev2, hev3] with ν h1 h2 h3
    have hb := h1 _ h2
    have hσpos : 0 < σ ν := by linarith
    have hmpos : (0 : ℝ) < m ν := by exact_mod_cast hm0 ν
    have hcm : cmk P S α β c A t (k ν) (m ν) = √(k ν : ℝ) / σ ν * (β - p ν) := rfl
    rw [hcm]
    have hrw : √(k ν : ℝ) / σ ν * (β - p ν) + t - g ν = √(k ν : ℝ) / σ ν * (F ν - p ν) := by
      simp only [hgdef]; ring
    rw [hrw, abs_mul, abs_of_pos (div_pos (hskpos ν) hσpos), abs_sub_comm]
    have hb' : |p ν - F ν| ≤ |C| / m ν :=
      hb.trans (div_le_div_of_nonneg_right (le_abs_self C) hmpos.le)
    calc √(k ν : ℝ) / σ ν * |p ν - F ν| ≤ √(k ν : ℝ) / σ ν * (|C| / m ν) :=
          mul_le_mul_of_nonneg_left hb' (div_pos (hskpos ν) hσpos).le
      _ ≤ √(k ν : ℝ) / (σ0 / 2) * (|C| / m ν) := by
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (abs_nonneg _) hmpos.le)
          exact div_le_div_of_nonneg_left (hskpos ν).le (by linarith) h3.le
      _ = 2 * |C| / σ0 * √(k ν : ℝ) / m ν := by field_simp
end CoVaRThm3Aux

open CoVaRThm3Aux

open CoVaRMC.Batching in
theorem solution (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop) :
    (∀ c0 : ℝ, c0 ≠ 0 → Tendsto (fun ν => √(k ν : ℝ) / m ν) atTop (𝓝 c0) →
      OPr P (fun ν ω => YBE S α β (k ν) (m ν) ω - c)
        (fun ν => ((k ν * m ν : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
    (Tendsto (fun ν => √(k ν : ℝ) / m ν) atTop (𝓝 0) →
      TendstoInDistribution (fun ν ω => √(k ν : ℝ) * (YBE S α β (k ν) (m ν) ω - c)) atTop id
        (fun _ => P) (gaussianReal 0 (β * (1 - β) / D.condDensity c v ^ 2).toNNReal)) := by
  have hA1' := hA1
  obtain ⟨h𝒳o, hv𝒳, h𝒴o, hc𝒴, -, -, -, -, -⟩ := hA1'
  have hcd := CoVaRMC.Batching.cond_density D Fc v c 𝒳 𝒴 hFc hA1 v hv𝒳 c hc𝒴
  set A := Aconst D β v c with hAdef
  set σ0 := √(β * (1 - β)) with hσ0
  have hσ0pos : 0 < σ0 := Real.sqrt_pos.mpr (mul_pos hβ.1 (by linarith [hβ.2]))
  have hApos : 0 < A := by
    simp only [hAdef, Aconst]
    exact div_pos hσ0pos hcd.2
  set Φ := cdf (gaussianReal 0 1) with hΦ
  set V : ℕ → Ω → ℝ := fun ν ω => √(k ν : ℝ) / A * (YBE S α β (k ν) (m ν) ω - c) with hVdef
  have hYm : ∀ ν, Measurable (fun ω => YBE S α β (k ν) (m ν) ω) := fun ν =>
    measurable_YBE S hSm α β (k ν) (m ν)
  have hVm : ∀ ν, Measurable (V ν) := fun ν =>
    measurable_const.mul ((hYm ν).sub measurable_const)
  have hsk : Tendsto (fun ν => √(k ν : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hk)
  have hskpos : ∀ ν, 0 < √(k ν : ℝ) := fun ν => Real.sqrt_pos.mpr (by exact_mod_cast hk0 ν)
  have h31 : ∀ t, ∃ C : ℝ, ∀ᶠ ν in atTop,
      |P.real {ω | V ν ω ≤ t} - Φ (-cmk P S α β c A t (k ν) (m ν))| ≤ C / √(k ν : ℝ) :=
    fun t => CoVaRMC.Batching.eq_31 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
      P S hSm hSi hSl k m hk0 hm0 hk hm t
  have hCk : ∀ C : ℝ, Tendsto (fun ν => C / √(k ν : ℝ)) atTop (𝓝 0) := fun C =>
    tendsto_const_nhds.div_atTop hsk
  refine ⟨?_, ?_⟩
  · -- Part (a)
    intro c0 hc0 hlim
    have hc0nn : 0 ≤ c0 := ge_of_tendsto' hlim (fun ν => by positivity)
    have hc0pos : 0 < c0 := lt_of_le_of_ne hc0nn (Ne.symm hc0)
    obtain ⟨K, hK0, hU⟩ := eq32_uniform D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM hM1 hM2
      P S hSm hSi hSl k m hk0 hm0 hk hm
    simp only [← hAdef] at hU
    set L := 1 + K * (2 * c0) with hLdef
    have hratio : ∀ᶠ ν in atTop, √(k ν : ℝ) / m ν ≤ 2 * c0 :=
      hlim.eventually (ge_mem_nhds (by linarith))
    have hbound : ∀ t, ∀ᶠ ν in atTop, |cmk P S α β c A t (k ν) (m ν) + t| ≤ L := by
      intro t
      obtain ⟨g, hg, hgev⟩ := hU t
      have hg1 : ∀ᶠ ν in atTop, |g ν| ≤ 1 := by
        have := (tendsto_zero_iff_abs_tendsto_zero _).mp hg
        exact this.eventually (ge_mem_nhds (by norm_num))
      filter_upwards [hgev, hg1, hratio] with ν h1 h2 h3
      have h4 : K * √(k ν : ℝ) / m ν ≤ K * (2 * c0) := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h3 hK0
      have := abs_sub_abs_le_abs_sub (cmk P S α β c A t (k ν) (m ν) + t) (g ν)
      rw [hLdef]; linarith
    -- tail bound for `V`
    have htail : ∀ η > 0, ∃ T > 0, ∀ᶠ ν in atTop, P.real {ω | T < |V ν ω|} ≤ η := by
      intro η hη
      have hΦL : Tendsto (fun T : ℝ => Φ (L - T)) atTop (𝓝 0) :=
        (tendsto_cdf_atBot (gaussianReal 0 1)).comp
          (tendsto_atBot_add_const_left _ L tendsto_neg_atTop_atBot)
      obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hΦL.eventually (gt_mem_nhds (by linarith : 0 < η / 4)))
      set T := max T0 1 with hTdef
      have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
      have hΦT : Φ (L - T) < η / 4 := hT0 T (le_max_left _ _)
      obtain ⟨Cp, hCp⟩ := h31 T
      obtain ⟨Cm, hCm⟩ := h31 (-T)
      refine ⟨T, hTpos, ?_⟩
      filter_upwards [hCp, hCm, hbound T, hbound (-T),
        (hCk Cp).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < η / 4)),
        (hCk Cm).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < η / 4))]
        with ν h1 h2 h3 h4 h5 h6
      have hmono := monotone_cdf (gaussianReal 0 1)
      -- lower tail
      have hlow : P.real {ω | V ν ω ≤ -T} ≤ η / 2 := by
        have e1 := (abs_le.mp h2).2
        have e2 : Φ (-cmk P S α β c A (-T) (k ν) (m ν)) ≤ Φ (L - T) :=
          hmono (by linarith [(abs_le.mp h4).1])
        linarith
      -- upper tail
      have hupp : 1 - η / 2 ≤ P.real {ω | V ν ω ≤ T} := by
        have e1 := (abs_le.mp h1).1
        have e2 : Φ (T - L) ≤ Φ (-cmk P S α β c A T (k ν) (m ν)) :=
          hmono (by linarith [(abs_le.mp h3).2])
        have e3 : Φ (T - L) = 1 - Φ (L - T) := by
          rw [show T - L = -(L - T) by ring, Phi_neg]
        linarith
      have hsub : {ω | T < |V ν ω|} ⊆ {ω | V ν ω ≤ -T} ∪ {ω | V ν ω ≤ T}ᶜ := by
        intro ω hω
        simp only [Set.mem_ofPred_eq] at hω
        rcases lt_abs.mp hω with h | h
        · right; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]; exact h
        · left; simp only [Set.mem_ofPred_eq]; linarith
      calc P.real {ω | T < |V ν ω|}
          ≤ P.real ({ω | V ν ω ≤ -T} ∪ {ω | V ν ω ≤ T}ᶜ) := measureReal_mono hsub
        _ ≤ P.real {ω | V ν ω ≤ -T} + P.real {ω | V ν ω ≤ T}ᶜ := measureReal_union_le _ _
        _ = P.real {ω | V ν ω ≤ -T} + (1 - P.real {ω | V ν ω ≤ T}) := by
            rw [measureReal_compl (measurableSet_le (hVm ν) measurable_const), probReal_univ]
        _ ≤ η := by linarith
    -- the rate factor
    set q : ℕ → ℝ := fun ν => ((k ν * m ν : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)) with hqdef
    have hqpos : ∀ ν, 0 < q ν := fun ν => Real.rpow_pos_of_pos (by
      have := hk0 ν; have := hm0 ν; positivity) _
    have hρ : Tendsto (fun ν => √(k ν : ℝ) * q ν) atTop (𝓝 (c0 ^ (1 / 3 : ℝ))) := by
      have : (fun ν => √(k ν : ℝ) * q ν) = fun ν => (√(k ν : ℝ) / m ν) ^ (1 / 3 : ℝ) := by
        funext ν; exact rate_identity (k ν) (m ν) (hk0 ν) (hm0 ν)
      rw [this]
      exact hlim.rpow_const (Or.inr (by norm_num))
    set ρ0 := c0 ^ (1 / 3 : ℝ) / 2 with hρ0
    have hρ0pos : 0 < ρ0 := by positivity
    have hρev : ∀ᶠ ν in atTop, ρ0 ≤ √(k ν : ℝ) * q ν :=
      hρ.eventually (le_mem_nhds (by linarith))
    apply opr_of_eventually P _ (fun ν => ((hYm ν).sub measurable_const).div_const _)
    intro ε hε
    obtain ⟨T, hT, hTev⟩ := htail ε hε
    refine ⟨T * A / ρ0, by positivity, ?_⟩
    filter_upwards [hTev, hρev] with ν h1 h2
    refine le_trans (measure_mono (t := {ω | T < |V ν ω|}) ?_) ?_
    · intro ω hω
      simp only [Set.mem_ofPred_eq, Pi.sub_apply] at hω ⊢
      rw [abs_div, abs_of_pos (hqpos ν), lt_div_iff₀ (hqpos ν)] at hω
      simp only [hVdef]
      rw [abs_mul, abs_of_pos (div_pos (hskpos ν) hApos), div_mul_eq_mul_div, lt_div_iff₀ hApos]
      have hTA : 0 ≤ T * A / ρ0 := by positivity
      calc T * A = T * A / ρ0 * ρ0 := by field_simp
        _ ≤ T * A / ρ0 * (√(k ν : ℝ) * q ν) := mul_le_mul_of_nonneg_left h2 hTA
        _ = √(k ν : ℝ) * (T * A / ρ0 * q ν) := by ring
        _ < √(k ν : ℝ) * |YBE S α β (k ν) (m ν) ω - c| := mul_lt_mul_of_pos_left hω (hskpos ν)
    · rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε.le]
      exact h1
  · -- Part (b)
    intro h0
    have hV : ∀ t, Tendsto (fun ν => P.real {ω | V ν ω ≤ t}) atTop (𝓝 (Φ t)) := by
      intro t
      obtain ⟨C, hC⟩ := h31 t
      obtain ⟨g, C2, hg, hC2⟩ := CoVaRMC.Batching.eq_32 D Fc α β hα hβ v c 𝒳 𝒴 hFc hA1 hv hc M hM
        hM1 hM2 P S hSm hSi hSl k m hk0 hm0 hk hm t
      simp only [← hAdef] at hC2
      have hcm : Tendsto (fun ν => cmk P S α β c A t (k ν) (m ν)) atTop (𝓝 (-t)) := by
        have hz : Tendsto (fun ν => cmk P S α β c A t (k ν) (m ν) + t) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_abs_tendsto_zero]
          have hb : Tendsto (fun ν => |g ν| + |C2| * (√(k ν : ℝ) / m ν)) atTop (𝓝 0) := by
            have := ((tendsto_zero_iff_abs_tendsto_zero _).mp hg).add (h0.const_mul |C2|)
            simpa only [zero_add, mul_zero, Function.comp_apply] using this
          refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hb
          filter_upwards [hC2] with ν h
          have hm' : (0 : ℝ) < m ν := by exact_mod_cast hm0 ν
          have e1 : C2 * √(k ν : ℝ) / m ν ≤ |C2| * (√(k ν : ℝ) / m ν) := by
            rw [mul_div_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg (hskpos ν).le hm'.le)
          have := abs_sub_abs_le_abs_sub (cmk P S α β c A t (k ν) (m ν) + t) (g ν)
          simp only [Function.comp_apply]
          linarith
        simpa using hz.sub_const t
      have hΦc : Tendsto (fun ν => Φ (-cmk P S α β c A t (k ν) (m ν))) atTop (𝓝 (Φ t)) := by
        have h2 : Tendsto (fun ν => -cmk P S α β c A t (k ν) (m ν)) atTop (𝓝 t) := by
          simpa using hcm.neg
        exact (continuous_Phi.tendsto t).comp h2
      have hd : Tendsto (fun ν => P.real {ω | V ν ω ≤ t} - Φ (-cmk P S α β c A t (k ν) (m ν)))
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_abs_tendsto_zero]
        exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hC (hCk C)
      simpa using hd.add hΦc
    -- identify the limit law
    have hnn : (0 : ℝ) ≤ β * (1 - β) / D.condDensity c v ^ 2 :=
      div_nonneg (mul_pos hβ.1 (sub_pos.2 hβ.2)).le (sq_nonneg _)
    have hvar : NNReal.mk (A ^ 2) (sq_nonneg _) * 1 =
        (β * (1 - β) / D.condDensity c v ^ 2).toNNReal := by
      ext
      rw [Real.coe_toNNReal _ hnn]
      simp only [NNReal.coe_mk, mul_one]
      simp only [hAdef, Aconst, div_pow]
      rw [Real.sq_sqrt (mul_pos hβ.1 (by linarith [hβ.2])).le]
    have hlaw : gaussianReal 0 (β * (1 - β) / D.condDensity c v ^ 2).toNNReal =
        (gaussianReal 0 1).map (A * ·) := by
      rw [gaussianReal_map_const_mul, mul_zero, hvar]
    apply tendstoInDist_of_cdf P _ (fun ν => measurable_const.mul ((hYm ν).sub measurable_const))
    intro s
    have hcdf : cdf (gaussianReal 0 (β * (1 - β) / D.condDensity c v ^ 2).toNNReal) s =
        Φ (s / A) := by
      have : IsProbabilityMeasure ((gaussianReal 0 1).map (A * ·)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      rw [hlaw, cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic, hΦ, cdf_eq_real]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic]
      rw [le_div_iff₀ hApos, mul_comm]
    rw [hcdf]
    have hset : ∀ ν, {ω | √(k ν : ℝ) * (YBE S α β (k ν) (m ν) ω - c) ≤ s} =
        {ω | V ν ω ≤ s / A} := by
      intro ν
      ext ω
      change √(k ν : ℝ) * _ ≤ s ↔ √(k ν : ℝ) / A * _ ≤ s / A
      rw [le_div_iff₀ hApos, div_mul_eq_mul_div, div_mul_cancel₀ _ hApos.ne']
    refine (hV (s / A)).congr fun ν => ?_
    exact congrArg P.real (hset ν).symm
