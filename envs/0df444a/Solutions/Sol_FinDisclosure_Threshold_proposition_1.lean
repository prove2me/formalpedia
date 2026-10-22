-- Prove2me | solution 1 for FinDisclosure.Threshold.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:30:16.231672+00:00
-- url     : https://prove2.me/submissions/29edc66a-fc13-483b-9b17-11d64d5415ab

import Mathlib
import Definitions.Def_FinDisclosure_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace FDProp1Aux
open FinDisclosure.Threshold

/-! ### Posterior expectations -/

theorem postExp_eq (μ : Measure ℝ) (h : ℝ → ℝ) (hi : IntegrableOn h (Icc 0 1) μ) :
    postExp μ h = ∫ s in Icc (0:ℝ) 1, h s ∂μ := by
  unfold postExp
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]

theorem postExp_nonneg (μ : Measure ℝ) (h : ℝ → ℝ) (hh : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ h s) :
    0 ≤ postExp μ h := by
  unfold postExp
  have : ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (-h s) ∂μ = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => 0)]
    · simp
    · intro s hs
      simp only
      rw [ENNReal.ofReal_eq_zero]
      linarith [hh s hs]
  rw [this]
  simp

theorem postExp_congr (μ : Measure ℝ) (h h' : ℝ → ℝ) (he : EqOn h h' (Icc 0 1)) :
    postExp μ h = postExp μ h' := by
  unfold postExp
  have e1 : ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (h s) ∂μ =
      ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (h' s) ∂μ :=
    setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp [he hs])
  have e2 : ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (-h s) ∂μ =
      ∫⁻ s in Icc (0:ℝ) 1, ENNReal.ofReal (-h' s) ∂μ :=
    setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp [he hs])
  rw [e1, e2]

theorem measurable_setLIntegral_K (F : ℝ → ENNReal) (hF : Measurable F) :
    Measurable (fun μ : Measure ℝ => ∫⁻ s in Icc (0:ℝ) 1, F s ∂μ) := by
  have : (fun μ : Measure ℝ => ∫⁻ s in Icc (0:ℝ) 1, F s ∂μ) =
      fun μ => ∫⁻ s, (Icc (0:ℝ) 1).indicator F s ∂μ := by
    funext μ; rw [lintegral_indicator measurableSet_Icc]
  rw [this]
  exact Measure.measurable_lintegral (hF.indicator measurableSet_Icc)

theorem measurable_postExp (h : ℝ → ℝ) (hh : Measurable h) :
    Measurable (fun μ : Measure ℝ => postExp μ h) := by
  unfold postExp
  exact ((measurable_setLIntegral_K _ (ENNReal.measurable_ofReal.comp hh)).ennreal_toReal).sub
    ((measurable_setLIntegral_K _ (ENNReal.measurable_ofReal.comp hh.neg)).ennreal_toReal)

theorem measurable_payoff (c : ℝ → ℝ) (I B lam : ℝ) (hc : Measurable c) :
    Measurable (fun μ => payoff c I B lam μ) := by
  unfold payoff price
  have h1 : Measurable (fun μ : Measure ℝ => postExp μ c) := measurable_postExp c hc
  have h2 : Measurable (fun μ : Measure ℝ => postExp μ (fun s => s - c s + B)) :=
    measurable_postExp _ ((measurable_id.sub hc).add measurable_const)
  refine Measurable.ite (measurableSet_le measurable_const h1) ?_ measurable_const
  exact h2.add (measurable_const.mul (h1.sub measurable_const))

theorem payoff_nonneg (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (μ : Measure ℝ) : 0 ≤ payoff c I B lam μ := by
  unfold payoff
  split_ifs with h
  · have h1 : 0 ≤ postExp μ (fun s => s - c s + B) := by
      apply postExp_nonneg
      intro s hs
      have := (hS.c_range s hs).2
      linarith [hS.B_pos]
    have h2 : 0 ≤ lam * (price c μ - I) := mul_nonneg hS.lam_nonneg (by linarith)
    linarith
  · exact le_rfl

theorem payoff_congr (c c' : ℝ → ℝ) (I B lam : ℝ) (he : EqOn c c' (Icc 0 1)) (μ : Measure ℝ) :
    payoff c I B lam μ = payoff c' I B lam μ := by
  unfold payoff price
  rw [postExp_congr μ c c' he,
    postExp_congr μ (fun s => s - c s + B) (fun s => s - c' s + B)
      (fun s hs => by simp [he hs])]

/-! ### The prior -/

theorem prior_restrict_K (f0 : ℝ → ℝ) : (prior f0).restrict (Icc 0 1) = prior f0 := by
  unfold prior
  rw [restrict_withDensity measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    inter_self]

theorem prior_univ (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hf : Continuous f0) : prior f0 univ = 1 := by
  unfold prior
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hf.integrableOn_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc hS.f0_nonneg),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hS.f0_int]
  simp

theorem prior_isProb (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hf : Continuous f0) : IsProbabilityMeasure (prior f0) :=
  ⟨prior_univ c f0 I B lam hS hf⟩

theorem integrable_prior (f0 : ℝ → ℝ) [IsFiniteMeasure (prior f0)] (F : ℝ → ℝ)
    (hF : Continuous F) : Integrable F (prior f0) := by
  have : IntegrableOn F (Icc 0 1) (prior f0) := hF.integrableOn_Icc
  rwa [IntegrableOn, prior_restrict_K] at this

theorem integral_prior_Ici (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hf : Continuous f0) (F : ℝ → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ s in Ici t, F s ∂(prior f0) = ∫ s in t..1, F s * f0 s := by
  unfold prior
  rw [restrict_withDensity measurableSet_Ici,
    integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici t ∩ Icc (0:ℝ) 1 = Icc (max t 0) 1 := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]; tauto
  rw [hset, max_eq_left ht0, intervalIntegral.integral_of_le ht1, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hS.f0_nonneg x ⟨by linarith [hx.1], hx.2⟩), mul_comm]

/-! ### The upper bound -/

theorem main_bound (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hf : Continuous f0) (τ : Measure (Measure ℝ)) (hτ : IsBayesPlausible (prior f0) τ)
    (ψ : ℝ → ℝ) (hψm : Measurable ψ) (hψ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ψ s) (M : ℝ)
    (hM : ∀ s ∈ Icc (0:ℝ) 1, ψ s ≤ M)
    (hbd : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      payoff c I B lam μ ≤ ∫ s in Icc (0:ℝ) 1, ψ s ∂μ) :
    value c I B lam τ ≤ ∫ s in Icc (0:ℝ) 1, ψ s ∂(prior f0) := by
  obtain ⟨_, hτae, hjoin⟩ := hτ
  haveI := prior_isProb c f0 I B lam hS hf
  set F : ℝ → ENNReal := (Icc (0:ℝ) 1).indicator (fun s => ENNReal.ofReal (ψ s)) with hFdef
  have hFm : Measurable F := hψm.ennreal_ofReal.indicator measurableSet_Icc
  have key : ∀ μ : Measure ℝ, ∫ s in Icc (0:ℝ) 1, ψ s ∂μ = (∫⁻ s, F s ∂μ).toReal := by
    intro μ
    rw [hFdef, lintegral_indicator measurableSet_Icc, integral_eq_lintegral_of_nonneg_ae]
    · exact ae_restrict_of_forall_mem measurableSet_Icc hψ0
    · exact hψm.aestronglyMeasurable
  have hfin : ∫⁻ s, F s ∂(prior f0) ≠ ⊤ := by
    have h1 : ∫⁻ s, F s ∂(prior f0) ≤ ∫⁻ _, ENNReal.ofReal M ∂(prior f0) := by
      apply lintegral_mono
      intro s
      by_cases hs : s ∈ Icc (0:ℝ) 1
      · simp only [hFdef, indicator_of_mem hs]
        exact ENNReal.ofReal_le_ofReal (hM s hs)
      · simp [hFdef, indicator_of_notMem hs]
    refine ne_top_of_le_ne_top ?_ h1
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hjl : ∫⁻ μ, ∫⁻ s, F s ∂μ ∂τ = ∫⁻ s, F s ∂(prior f0) := by
    rw [← hjoin, Measure.lintegral_join hFm.aemeasurable]
  have hΦm : Measurable (fun μ : Measure ℝ => ∫⁻ s, F s ∂μ) := Measure.measurable_lintegral hFm
  have hint : Integrable (fun μ : Measure ℝ => (∫⁻ s, F s ∂μ).toReal) τ :=
    integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable (by rw [hjl]; exact hfin)
  calc value c I B lam τ = ∫ μ, payoff c I B lam μ ∂τ := rfl
    _ ≤ ∫ μ, (∫⁻ s, F s ∂μ).toReal ∂τ := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun μ => payoff_nonneg c f0 I B lam hS μ) hint
        filter_upwards [hτae] with μ hμ
        rw [← key μ]
        exact hbd μ hμ
    _ = (∫⁻ s, F s ∂(prior f0)).toReal := by
        rw [integral_toReal hΦm.aemeasurable (ae_lt_top hΦm (by rw [hjl]; exact hfin)), hjl]
    _ = ∫ s in Icc (0:ℝ) 1, ψ s ∂(prior f0) := (key _).symm

theorem payoff_le_fin (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hc : Continuous c) (μ : Measure ℝ) [IsProbabilityMeasure μ] (hfin : I ≤ price c μ)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    payoff c I B lam μ ≤ ∫ s in Icc (0:ℝ) 1, (gE c I B lam s + κ * (c s - I)) ∂μ := by
  have e1 : price c μ = ∫ s in Icc (0:ℝ) 1, c s ∂μ := postExp_eq μ c hc.integrableOn_Icc
  have hr : Continuous (fun s : ℝ => s - c s + B) := by fun_prop
  have e2 : postExp μ (fun s => s - c s + B) = ∫ s in Icc (0:ℝ) 1, (s - c s + B) ∂μ :=
    postExp_eq μ _ hr.integrableOn_Icc
  have e3 : ∫ s in Icc (0:ℝ) 1, (gE c I B lam s + κ * (c s - I)) ∂μ =
      ∫ s in Icc (0:ℝ) 1, (s - c s + B) ∂μ + (lam + κ) * ∫ s in Icc (0:ℝ) 1, c s ∂μ
        - (μ (Icc (0:ℝ) 1)).toReal * ((lam + κ) * I) := by
    have : ∀ s, gE c I B lam s + κ * (c s - I) = ((s - c s + B) + (lam + κ) * c s) - (lam + κ) * I := by
      intro s; simp only [gE]; ring
    simp_rw [this]
    rw [integral_sub, integral_add, integral_const_mul, setIntegral_const]
    · simp [Measure.real]
    · exact hr.integrableOn_Icc
    · exact (hc.const_mul _).integrableOn_Icc
    · exact (hr.add (hc.const_mul _)).integrableOn_Icc
    · exact continuous_const.integrableOn_Icc
  have hm : (μ (Icc (0:ℝ) 1)).toReal ≤ 1 := by
    have := prob_le_one (μ := μ) (s := Icc (0:ℝ) 1)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hm0 : 0 ≤ (μ (Icc (0:ℝ) 1)).toReal := ENNReal.toReal_nonneg
  unfold payoff
  rw [if_pos hfin, e2, e3]
  rw [e1] at hfin ⊢
  have h1 : 0 ≤ κ * (∫ s in Icc (0:ℝ) 1, c s ∂μ - I) := mul_nonneg hκ (by linarith)
  have h2 : 0 ≤ (1 - (μ (Icc (0:ℝ) 1)).toReal) * ((lam + κ) * I) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith [hS.lam_nonneg]) hS.I_pos.le)
  nlinarith

/-! ### The threshold policy -/

theorem measurableSet_isProb :
    MeasurableSet {μ : Measure ℝ | IsProbabilityMeasure μ} := by
  have : {μ : Measure ℝ | IsProbabilityMeasure μ} = (fun μ : Measure ℝ => μ univ) ⁻¹' {1} := by
    ext μ; simp [isProbabilityMeasure_iff]
  rw [this]
  exact Measure.measurable_coe MeasurableSet.univ (measurableSet_singleton 1)

theorem thr_BP (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hf : Continuous f0) (t : ℝ) :
    IsBayesPlausible (prior f0) (thresholdPolicy f0 t) := by
  haveI := prior_isProb c f0 I B lam hS hf
  unfold thresholdPolicy revealPolicy
  set μ0 := prior f0
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [measure_add_measure_compl measurableSet_Ici, measure_univ]
  · rw [ae_add_measure_iff]
    constructor
    · by_cases ha : μ0 (Ici t) = 0
      · rw [ha, zero_smul]; simp
      · apply Measure.ae_smul_measure
        rw [ae_dirac_iff measurableSet_isProb]
        exact cond_isProbabilityMeasure ha
    · by_cases ha : μ0 (Ici t)ᶜ = 0
      · rw [ha, zero_smul]; simp
      · apply Measure.ae_smul_measure
        rw [ae_dirac_iff measurableSet_isProb]
        exact cond_isProbabilityMeasure ha
  · ext s hs
    rw [Measure.join_apply hs, lintegral_add_measure, lintegral_smul_measure,
      lintegral_smul_measure, lintegral_dirac' _ (Measure.measurable_coe hs),
      lintegral_dirac' _ (Measure.measurable_coe hs)]
    rw [← cond_add_cond_compl_eq (t := s) measurableSet_Ici μ0]
    simp only [smul_eq_mul]
    ring

theorem cond_setIntegral (μ0 : Measure ℝ) (hK : μ0.restrict (Icc 0 1) = μ0) (A : Set ℝ)
    (hA : MeasurableSet A) (h : ℝ → ℝ) :
    ∫ s in Icc (0:ℝ) 1, h s ∂(μ0[|A]) =
      (μ0 A).toReal⁻¹ * ∫ s in A, h s ∂μ0 := by
  rw [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure,
    Measure.restrict_restrict measurableSet_Icc, inter_comm,
    ← Measure.restrict_restrict hA, hK, ENNReal.toReal_inv, smul_eq_mul]

theorem thr_value_ge (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hc : Continuous c) (hf : Continuous f0) (t : ℝ)
    (hG : ∫ s in Ici t, (c s - I) ∂(prior f0) = 0) :
    ∫ s in Ici t, gE c I B lam s ∂(prior f0) ≤ value c I B lam (thresholdPolicy f0 t) := by
  haveI := prior_isProb c f0 I B lam hS hf
  have hpm := measurable_payoff c I B lam hc.measurable
  have hnn := payoff_nonneg c f0 I B lam hS
  unfold value thresholdPolicy revealPolicy
  set μ0 := prior f0
  set A := Ici t
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    hpm.aestronglyMeasurable]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hpm.ennreal_ofReal, lintegral_dirac' _ hpm.ennreal_ofReal]
  have key : ∫ s in A, gE c I B lam s ∂μ0 = (μ0 A).toReal * payoff c I B lam (μ0[|A]) := by
    by_cases ha : μ0 A = 0
    · rw [Measure.restrict_eq_zero.mpr ha, integral_zero_measure, ha]; simp
    · have hxP : IsProbabilityMeasure (μ0[|A]) := cond_isProbabilityMeasure ha
      have hcI : ∫ s in A, c s ∂μ0 = (μ0 A).toReal * I := by
        have h1 : ∫ s in A, (c s - I) ∂μ0 = ∫ s in A, c s ∂μ0 - (μ0 A).toReal * I := by
          rw [integral_sub, setIntegral_const]
          · simp [Measure.real]
          · exact (integrable_prior f0 c hc).integrableOn
          · exact (integrable_prior f0 _ continuous_const).integrableOn
        linarith
      have hat : (μ0 A).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨ha, measure_ne_top _ _⟩
      have hprice : price c (μ0[|A]) = I := by
        unfold price
        rw [postExp_eq _ _ hc.integrableOn_Icc, cond_setIntegral μ0 (prior_restrict_K f0) A measurableSet_Ici, hcI]
        field_simp
      have hr : Continuous (fun s : ℝ => s - c s + B) := by fun_prop
      unfold payoff
      rw [hprice, if_pos le_rfl, postExp_eq _ _ hr.integrableOn_Icc,
        cond_setIntegral μ0 (prior_restrict_K f0) A measurableSet_Ici]
      have hg : ∫ s in A, gE c I B lam s ∂μ0 =
          ∫ s in A, (s - c s + B) ∂μ0 + lam * ∫ s in A, (c s - I) ∂μ0 := by
        unfold gE
        rw [← integral_const_mul, ← integral_add]
        · exact (integrable_prior f0 _ hr).integrableOn
        · exact (integrable_prior f0 _ ((hc.sub continuous_const).const_mul lam)).integrableOn
      rw [hg, hG, mul_zero, add_zero, sub_self, mul_zero, add_zero, ← mul_assoc,
        mul_inv_cancel₀ hat, one_mul]
  rw [key, ← ENNReal.toReal_ofReal (hnn (μ0[|A])), ← ENNReal.toReal_mul]
  apply ENNReal.toReal_mono
  · exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top⟩
  · rw [ENNReal.toReal_ofReal (hnn _)]
    exact le_self_add

/-! ### The threshold `ŝ` -/

theorem exists_shat (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hc : Continuous c) (hf : Continuous f0) (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) :
    ∃ shat : ℝ, 0 < shat ∧ shat ≤ 1 ∧ ∫ s in shat..1, (c s - I) * f0 s = 0 ∧
      ∀ s, 0 ≤ s → s < shat → c s < I := by
  set G : ℝ → ℝ := fun t => ∫ s in t..1, (c s - I) * f0 s with hGdef
  have hk : Continuous (fun s => (c s - I) * f0 s) := by fun_prop
  have hGc : Continuous G := by
    have : G = fun t => -∫ s in (1:ℝ)..t, (c s - I) * f0 s := by
      funext t; simp only [hGdef]; rw [intervalIntegral.integral_symm]
    rw [this]
    exact (intervalIntegral.continuous_primitive (fun a b => hk.intervalIntegrable a b) 1).neg
  have hG0 : G 0 < 0 := by
    simp only [hGdef]
    have : ∫ s in (0:ℝ)..1, (c s - I) * f0 s =
        (∫ s in (0:ℝ)..1, c s * f0 s) - I * ∫ s in (0:ℝ)..1, f0 s := by
      have e : (fun s => (c s - I) * f0 s) = fun s => c s * f0 s - I * f0 s := by
        funext s; ring
      rw [e, intervalIntegral.integral_sub ((by fun_prop : Continuous fun s => c s * f0 s).intervalIntegrable _ _)
        ((hf.const_mul I).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    rw [this, hS.f0_int, mul_one]; linarith
  have hG1 : G 1 = 0 := by simp [hGdef]
  set S := {t ∈ Icc (0:ℝ) 1 | G t = 0} with hSdef
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_eq hGc continuous_const)
  have hSne : S.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, hG1⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hmem : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  refine ⟨sInf S, ?_, hmem.1.2, hmem.2, ?_⟩
  · rcases lt_or_eq_of_le hmem.1.1 with h | h
    · exact h
    · exfalso; have := hmem.2; rw [← h] at this; linarith
  · intro s hs0 hsl
    by_contra hcs
    push Not at hcs
    have hs1 : s ≤ 1 := le_trans hsl.le hmem.1.2
    have hGs : 0 ≤ G s := by
      simp only [hGdef]
      apply intervalIntegral.integral_nonneg hs1
      intro u hu
      have hcu : c s ≤ c u := hS.c_mono ⟨hs0, hs1⟩ ⟨le_trans hs0 hu.1, hu.2⟩ hu.1
      exact mul_nonneg (by linarith) (hS.f0_nonneg u ⟨le_trans hs0 hu.1, hu.2⟩)
    obtain ⟨u, hu, hGu⟩ := intermediate_value_Icc hs0 hGc.continuousOn ⟨hG0.le, hGs⟩
    have : sInf S ≤ u := csInf_le hSbdd ⟨⟨hu.1, le_trans hu.2 hs1⟩, hGu⟩
    linarith [hu.2]

/-! ### The upper bound at `ŝ` -/

theorem upper (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hc : Continuous c) (hf : Continuous f0) (hB : lam * I ≤ B)
    (shat : ℝ) (h0 : 0 < shat) (h1 : shat ≤ 1)
    (hGi : ∫ s in shat..1, (c s - I) * f0 s = 0)
    (hGp : ∫ s in Ici shat, (c s - I) ∂(prior f0) = 0)
    (hlow : ∀ s, 0 ≤ s → s < shat → c s < I)
    (τ : Measure (Measure ℝ)) (hτ : IsBayesPlausible (prior f0) τ) :
    value c I B lam τ ≤ ∫ s in Ici shat, gE c I B lam s ∂(prior f0) := by
  have hP := prior_isProb c f0 I B lam hS hf
  have hgc : Continuous (gE c I B lam) := by unfold gE; fun_prop
  have hg0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ gE c I B lam s := by
    intro s hs
    have := hS.c_range s hs
    have : 0 ≤ lam * c s := mul_nonneg hS.lam_nonneg this.1
    unfold gE; nlinarith
  have hgM : ∀ s ∈ Icc (0:ℝ) 1, gE c I B lam s ≤ 2 + B := by
    intro s hs
    have h := hS.c_range s hs
    have : lam * c s ≤ 1 * 1 := mul_le_mul hS.lam_le_one (by linarith [hs.2]) h.1 zero_le_one
    have : 0 ≤ lam * I := mul_nonneg hS.lam_nonneg hS.I_pos.le
    unfold gE; nlinarith [hs.2]
  have hshK : shat ∈ Icc (0:ℝ) 1 := ⟨h0.le, h1⟩
  have hcle : c shat ≤ I := by
    have ht : Filter.Tendsto c (nhdsWithin shat (Iio shat)) (nhds (c shat)) :=
      hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsLT h0] with s hs
    exact (hlow s hs.1.le hs.2).le
  rcases lt_or_eq_of_le hcle with hA | hBc
  · -- Case A: a Lagrange multiplier for the financing constraint
    set κ := gE c I B lam shat / (I - c shat) with hκdef
    have hκ : 0 ≤ κ := div_nonneg (hg0 shat hshK) (by linarith)
    set φ : ℝ → ℝ := fun s => gE c I B lam s + κ * (c s - I) with hφdef
    have hφc : Continuous φ := by simp only [hφdef]; fun_prop
    have hφs : φ shat = 0 := by
      simp only [hφdef, hκdef]
      have : I - c shat ≠ 0 := by linarith
      field_simp
      ring
    have hφmono : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, a ≤ b → φ a ≤ φ b := by
      intro a ha b hb hab
      have e1 := hS.c_mono ha hb hab
      have e2 : a - c a ≤ b - c b := hS.resid_mono ha hb hab
      have e3 := mul_le_mul_of_nonneg_left e1 (add_nonneg hS.lam_nonneg hκ)
      simp only [hφdef, gE]
      nlinarith
    have hbd : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
        payoff c I B lam μ ≤ ∫ s in Icc (0:ℝ) 1, max (φ s) 0 ∂μ := by
      intro μ hμ
      by_cases hfin : I ≤ price c μ
      · calc payoff c I B lam μ ≤ ∫ s in Icc (0:ℝ) 1, φ s ∂μ :=
              payoff_le_fin c f0 I B lam hS hc μ hfin κ hκ
          _ ≤ ∫ s in Icc (0:ℝ) 1, max (φ s) 0 ∂μ :=
              setIntegral_mono_on hφc.integrableOn_Icc
                (hφc.max continuous_const).integrableOn_Icc measurableSet_Icc
                (fun s _ => le_max_left _ _)
      · unfold payoff; rw [if_neg hfin]
        exact setIntegral_nonneg measurableSet_Icc (fun s _ => le_max_right _ _)
    have hMb : ∀ s ∈ Icc (0:ℝ) 1, max (φ s) 0 ≤ 2 + B + κ := by
      intro s hs
      have h := hS.c_range s hs
      have : κ * (c s - I) ≤ κ * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [hs.2, hS.I_pos]) hκ
      apply max_le
      · simp only [hφdef]; linarith [hgM s hs]
      · linarith [hS.B_pos]
    have hmain := main_bound c f0 I B lam hS hf τ hτ (fun s => max (φ s) 0)
      (hφc.max continuous_const).measurable (fun s _ => le_max_right _ _) (2 + B + κ) hMb hbd
    refine le_trans hmain (le_of_eq ?_)
    calc ∫ s in Icc (0:ℝ) 1, max (φ s) 0 ∂(prior f0)
        = ∫ s in Icc (0:ℝ) 1, (Ici shat).indicator φ s ∂(prior f0) := by
          refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
          by_cases hs' : shat ≤ s
          · rw [indicator_of_mem (show s ∈ Ici shat from hs')]
            exact max_eq_left (hφs ▸ hφmono shat hshK s hs hs')
          · rw [indicator_of_notMem (show s ∉ Ici shat from hs')]
            push Not at hs'
            exact max_eq_right (hφs ▸ hφmono s hs shat hshK hs'.le)
      _ = ∫ s, (Ici shat).indicator φ s ∂(prior f0) := by rw [prior_restrict_K]
      _ = ∫ s in Ici shat, φ s ∂(prior f0) := integral_indicator measurableSet_Ici
      _ = ∫ s in Ici shat, gE c I B lam s ∂(prior f0) +
            κ * ∫ s in Ici shat, (c s - I) ∂(prior f0) := by
          simp only [hφdef]
          rw [integral_add, integral_const_mul]
          · exact (integrable_prior f0 _ hgc).integrableOn
          · exact (integrable_prior f0 _ ((hc.sub continuous_const).const_mul κ)).integrableOn
      _ = ∫ s in Ici shat, gE c I B lam s ∂(prior f0) := by rw [hGp]; ring
  · -- Case B: `c ŝ = I`, so `c ≡ I` above `ŝ`
    have hk : Continuous (fun s => (c s - I) * f0 s) := by fun_prop
    have hc1 : c 1 ≤ I := by
      by_contra hlt
      push Not at hlt
      have hs1 : shat < 1 := lt_of_le_of_ne h1 (fun h => by rw [h] at hBc; linarith)
      have ev1 : ∀ᶠ u in nhdsWithin (1:ℝ) (Iio 1), I < c u :=
        (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hlt)
      have ev2 : ∀ᶠ u in nhdsWithin (1:ℝ) (Iio 1), u ∈ Ioo shat 1 := Ioo_mem_nhdsLT hs1
      obtain ⟨u, hu1, hu2⟩ := (ev1.and ev2).exists
      have hpos : 0 < ∫ s in shat..1, (c s - I) * f0 s := by
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := u)
          (hk.intervalIntegrable _ _) (hk.intervalIntegrable _ _)]
        have p1 : 0 ≤ ∫ s in shat..u, (c s - I) * f0 s := by
          apply intervalIntegral.integral_nonneg hu2.1.le
          intro x hx
          have hxK : x ∈ Icc (0:ℝ) 1 := ⟨le_trans h0.le hx.1, le_trans hx.2 hu2.2.le⟩
          have := hS.c_mono hshK hxK hx.1
          exact mul_nonneg (by linarith) (hS.f0_nonneg x hxK)
        have p2 : (c u - I) * ∫ s in u..1, f0 s ≤ ∫ s in u..1, (c s - I) * f0 s := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_mono_on hu2.2.le
            ((hf.const_mul _).intervalIntegrable _ _) (hk.intervalIntegrable _ _)
          intro x hx
          have huK : u ∈ Icc (0:ℝ) 1 := ⟨le_trans h0.le hu2.1.le, hu2.2.le⟩
          have hxK : x ∈ Icc (0:ℝ) 1 := ⟨le_trans huK.1 hx.1, hx.2⟩
          have := hS.c_mono huK hxK hx.1
          exact mul_le_mul_of_nonneg_right (by linarith) (hS.f0_nonneg x hxK)
        have p3 : 0 < (c u - I) * ∫ s in u..1, f0 s :=
          mul_pos (by linarith) (hS.f0_supp u 1 (by linarith [hu2.1]) hu2.2 le_rfl)
        linarith
      linarith
    have hcK : ∀ s ∈ Icc (0:ℝ) 1, c s ≤ I := fun s hs =>
      le_trans (hS.c_mono hs ⟨zero_le_one, le_rfl⟩ hs.2) hc1
    set ψ : ℝ → ℝ := (Ici shat).indicator (gE c I B lam) with hψdef
    have hψm : Measurable ψ := hgc.measurable.indicator measurableSet_Ici
    have hψ0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ ψ s := by
      intro s hs
      by_cases hs' : s ∈ Ici shat
      · rw [hψdef, indicator_of_mem hs']; exact hg0 s hs
      · rw [hψdef, indicator_of_notMem hs']
    have hψM : ∀ s ∈ Icc (0:ℝ) 1, ψ s ≤ 2 + B := by
      intro s hs
      by_cases hs' : s ∈ Ici shat
      · rw [hψdef, indicator_of_mem hs']; exact hgM s hs
      · rw [hψdef, indicator_of_notMem hs']; linarith [hS.B_pos]
    have hbd : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
        payoff c I B lam μ ≤ ∫ s in Icc (0:ℝ) 1, ψ s ∂μ := by
      intro μ hμ
      by_cases hfin : I ≤ price c μ
      · have hle := payoff_le_fin c f0 I B lam hS hc μ hfin 0 le_rfl
        simp only [zero_mul, add_zero] at hle
        refine le_trans hle (le_of_eq ?_)
        have e1 : price c μ = ∫ s in Icc (0:ℝ) 1, c s ∂μ := postExp_eq μ c hc.integrableOn_Icc
        have hm : (μ (Icc (0:ℝ) 1)).toReal ≤ 1 := by
          have := prob_le_one (μ := μ) (s := Icc (0:ℝ) 1)
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
        have hint : ∫ s in Icc (0:ℝ) 1, (I - c s) ∂μ = 0 := by
          apply le_antisymm
          · rw [integral_sub, setIntegral_const]
            · simp only [Measure.real, smul_eq_mul]
              rw [e1] at hfin
              nlinarith [mul_nonneg (sub_nonneg.mpr hm) hS.I_pos.le]
            · exact continuous_const.integrableOn_Icc
            · exact hc.integrableOn_Icc
          · exact setIntegral_nonneg measurableSet_Icc (fun s hs => by linarith [hcK s hs])
        have hae : (fun s => I - c s) =ᵐ[μ.restrict (Icc (0:ℝ) 1)] 0 :=
          (integral_eq_zero_iff_of_nonneg_ae
            (ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => by simp only [Pi.zero_apply, Pi.sub_apply]; linarith [hcK s hs]))
            (continuous_const.sub hc).integrableOn_Icc).mp hint
        refine setIntegral_congr_ae measurableSet_Icc ?_
        filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hae] with s hs hsK
        have hcs : I - c s = 0 := hs hsK
        have hge : shat ≤ s := by
          by_contra hlt; push Not at hlt
          have := hlow s hsK.1 hlt
          linarith
        rw [hψdef, indicator_of_mem (show s ∈ Ici shat from hge)]
      · unfold payoff; rw [if_neg hfin]
        exact setIntegral_nonneg measurableSet_Icc hψ0
    have hmain := main_bound c f0 I B lam hS hf τ hτ ψ hψm hψ0 (2 + B) hψM hbd
    refine le_trans hmain (le_of_eq ?_)
    rw [prior_restrict_K, hψdef, integral_indicator measurableSet_Ici]

/-! ### Assembly (continuous data) -/

theorem core (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hc : Continuous c) (hf : Continuous f0)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) (hB : lam * I ≤ B) :
    ∃ shat : ℝ, 0 < shat ∧ shat ≤ 1 ∧ ∫ s in shat..1, (c s - I) * f0 s = 0 ∧
      IsBayesPlausible (prior f0) (thresholdPolicy f0 shat) ∧
      ∀ τ : Measure (Measure ℝ), IsBayesPlausible (prior f0) τ →
        value c I B lam τ ≤ value c I B lam (thresholdPolicy f0 shat) := by
  obtain ⟨shat, h0, h1, hG, hlow⟩ := exists_shat c f0 I B lam hS hc hf hEc
  have hGp : ∫ s in Ici shat, (c s - I) ∂(prior f0) = 0 :=
    (integral_prior_Ici c f0 I B lam hS hf (fun s => c s - I) shat h0.le h1).trans hG
  refine ⟨shat, h0, h1, hG, thr_BP c f0 I B lam hS hf shat, fun τ hτ => ?_⟩
  exact le_trans (upper c f0 I B lam hS hc hf hB shat h0 h1 hG hGp hlow τ hτ)
    (thr_value_ge c f0 I B lam hS hc hf shat hGp)

end FDProp1Aux

open FinDisclosure.Threshold in
theorem solution (c f0 : ℝ → ℝ) (I B lam : ℝ) (hS : Standing c f0 I B lam)
    (hEc : ∫ s in (0:ℝ)..1, c s * f0 s < I) (hB : lam * I ≤ B) :
    ∃ shat : ℝ, 0 < shat ∧ shat ≤ 1 ∧ ∫ s in shat..1, (c s - I) * f0 s = 0 ∧
      IsBayesPlausible (prior f0) (thresholdPolicy f0 shat) ∧
      ∀ τ : Measure (Measure ℝ), IsBayesPlausible (prior f0) τ →
        value c I B lam τ ≤ value c I B lam (thresholdPolicy f0 shat) := by
  set p : ℝ → ℝ := fun s => max 0 (min s 1) with hpdef
  have hp : Continuous p := continuous_const.max (continuous_id.min continuous_const)
  have hpK : ∀ s, p s ∈ Icc (0:ℝ) 1 :=
    fun s => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hpid : ∀ s ∈ Icc (0:ℝ) 1, p s = s := fun s hs => by
    simp only [hpdef, min_eq_left hs.2, max_eq_right hs.1]
  set c' : ℝ → ℝ := fun s => c (p s) with hc'def
  set f' : ℝ → ℝ := fun s => f0 (p s) with hf'def
  have hc' : Continuous c' := hS.c_cont.comp_continuous hp hpK
  have hf' : Continuous f' := hS.f0_cont.comp_continuous hp hpK
  have ec : EqOn c c' (Icc 0 1) := fun s hs => by simp only [hc'def, hpid s hs]
  have ef : EqOn f0 f' (Icc 0 1) := fun s hs => by simp only [hf'def, hpid s hs]
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → uIcc a b ⊆ Icc 0 1 := by
    intro a b ha hab hb x hx
    rw [uIcc_of_le hab] at hx
    exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩
  have hS' : Standing c' f' I B lam :=
    { I_pos := hS.I_pos, I_lt_one := hS.I_lt_one, B_pos := hS.B_pos,
      lam_nonneg := hS.lam_nonneg, lam_le_one := hS.lam_le_one,
      c_cont := hc'.continuousOn
      c_mono := hS.c_mono.congr ec
      resid_mono := hS.resid_mono.congr (fun s hs => by simp only [ec hs])
      c_range := fun s hs => by rw [← ec hs]; exact hS.c_range s hs
      f0_cont := hf'.continuousOn
      f0_nonneg := fun s hs => by rw [← ef hs]; exact hS.f0_nonneg s hs
      f0_int := by
        exact (intervalIntegral.integral_congr
          (fun s hs => (ef (hsub 0 1 le_rfl zero_le_one le_rfl hs)).symm)).trans hS.f0_int
      f0_supp := fun a b ha hab hb => by
        rw [intervalIntegral.integral_congr (g := f0)
          (fun s hs => (ef (hsub a b ha hab.le hb hs)).symm)]
        exact hS.f0_supp a b ha hab hb }
  have hprior : prior f' = prior f0 := by
    unfold prior
    exact withDensity_congr_ae
      (ae_restrict_of_forall_mem measurableSet_Icc (fun s hs => by simp only [ef hs]))
  have hthr : thresholdPolicy f' = thresholdPolicy f0 := by
    funext t; unfold thresholdPolicy; rw [hprior]
  have hval : ∀ τ, value c' I B lam τ = value c I B lam τ := fun τ => by
    unfold value; congr 1; funext μ; exact (FDProp1Aux.payoff_congr c c' I B lam ec μ).symm
  have hEc' : ∫ s in (0:ℝ)..1, c' s * f' s < I := by
    rwa [intervalIntegral.integral_congr (g := fun s => c s * f0 s)
      (fun s hs => by
        have h := hsub 0 1 le_rfl zero_le_one le_rfl hs
        simp only [← ec h, ← ef h])]
  obtain ⟨shat, h0, h1, hG, hBP, hopt⟩ := FDProp1Aux.core c' f' I B lam hS' hc' hf' hEc' hB
  refine ⟨shat, h0, h1, ?_, ?_, ?_⟩
  · rw [← hG]
    exact intervalIntegral.integral_congr (fun s hs => by
      have h := hsub shat 1 h0.le h1 le_rfl hs
      simp only [← ec h, ← ef h])
  · rw [← hprior, ← hthr]; exact hBP
  · intro τ hτ
    rw [← hval, ← hval, ← hthr]
    exact hopt τ (by rw [hprior]; exact hτ)
