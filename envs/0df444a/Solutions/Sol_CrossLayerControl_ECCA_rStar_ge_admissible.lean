-- Prove2me | solution 1 for CrossLayerControl.ECCA.rStar_ge_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T06:18:55.530681+00:00
-- url     : https://prove2.me/submissions/ba80dae3-be42-4024-be52-50e6392e7d07

import Mathlib
import Definitions.Def_CrossLayerControl_ECCA_Downlink
import Definitions.Def_CrossLayerControl_ECCA_RateHyp
import Definitions.Def_CrossLayerControl_ECCA_DownlinkMeas
import Definitions.Def_CrossLayerControl_ECCA_throughputAvg
import Definitions.Def_CrossLayerControl_ECCA_IsAdmissiblePolicy
import Definitions.Def_CrossLayerControl_ECCA_rStar

open MeasureTheory Filter Topology CrossLayerControl.ECCA
open scoped ENNReal

namespace RStarAux

/-- Integrals against the time-averaged law. -/
lemma avg_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (Pr : Measure α)
    (X : ℕ → α → β) (hX : ∀ τ, Measurable (X τ)) (t : ℕ) (ht : t ≠ 0)
    (f : β → ℝ) (hf : Measurable f) (hfi : ∀ τ, Integrable (fun ω => f (X τ ω)) Pr) :
    Integrable f ((t : ℝ≥0∞)⁻¹ • ∑ τ ∈ Finset.range t, Pr.map (X τ)) ∧
    ∫ x, f x ∂((t : ℝ≥0∞)⁻¹ • ∑ τ ∈ Finset.range t, Pr.map (X τ)) =
      (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, f (X τ ω) ∂Pr := by
  have hint : ∀ τ, Integrable f (Pr.map (X τ)) := fun τ =>
    (integrable_map_measure hf.aestronglyMeasurable (hX τ).aemeasurable).mpr (hfi τ)
  have hsum : Integrable f (∑ τ ∈ Finset.range t, Pr.map (X τ)) :=
    integrable_finsetSum_measure.mpr (fun τ _ => hint τ)
  have hne : (t : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (by exact_mod_cast ht)
  refine ⟨hsum.smul_measure hne, ?_⟩
  rw [integral_smul_measure, integral_finsetSum_measure (fun τ _ => hint τ)]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_map (hX τ).aemeasurable hf.aestronglyMeasurable]

lemma avg_bounds {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (g : ℕ → Ω → ℝ) (hg : ∀ τ, Integrable (g τ) Pr) (lo hi : ℝ)
    (h : ∀ τ ω, lo ≤ g τ ω ∧ g τ ω ≤ hi) (t : ℕ) (ht : 1 ≤ t) :
    lo ≤ (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, g τ ω ∂Pr ∧
      (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, g τ ω ∂Pr ≤ hi := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : ∀ τ, lo ≤ ∫ ω, g τ ω ∂Pr := fun τ => by
    have := integral_mono (integrable_const lo) (hg τ) (fun ω => (h τ ω).1)
    simpa using this
  have h2 : ∀ τ, ∫ ω, g τ ω ∂Pr ≤ hi := fun τ => by
    have := integral_mono (hg τ) (integrable_const hi) (fun ω => (h τ ω).2)
    simpa using this
  have s1 : (t : ℝ) * lo ≤ ∑ τ ∈ Finset.range t, ∫ ω, g τ ω ∂Pr := by
    have := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.range t) => h1 τ)
    simpa using this
  have s2 : ∑ τ ∈ Finset.range t, ∫ ω, g τ ω ∂Pr ≤ (t : ℝ) * hi := by
    have := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.range t) => h2 τ)
    simpa using this
  constructor
  · rw [le_inv_mul_iff₀ htpos]; linarith
  · rw [inv_mul_le_iff₀ htpos]; linarith

lemma integrable_of_bdd {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsFiniteMeasure Pr]
    (g : Ω → ℝ) (hg : Measurable g) (c : ℝ) (h : ∀ ω, |g ω| ≤ c) : Integrable g Pr :=
  Integrable.mono' (integrable_const c) hg.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using h ω)

end RStarAux

open RStarAux in
theorem solution {L : ℕ} {𝒮 : Type*} [MeasurableSpace 𝒮] (M : Downlink L 𝒮)
    (hM : RateHyp M) (hMm : DownlinkMeas M)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (A : ℕ → Ω → Fin L → ℝ) (S : ℕ → Ω → 𝒮) (R P : ℕ → Ω → Fin L → ℝ) (u₀ : Fin L → ℝ)
    (μ : Measure ((Fin L → ℝ) × 𝒮))
    (hAS : ∀ t, Measurable (fun ω => (A t ω, S t ω)))
    (hlaw : ∀ t, Pr.map (fun ω => (A t ω, S t ω)) = μ)
    (hA : ∀ t ω i, 0 ≤ A t ω i ∧ A t ω i ≤ M.Rhat)
    (hadm : IsAdmissiblePolicy M Pr A S R P u₀) :
    limsup (fun t : ℕ => (throughputAvg Pr R t : EReal)) atTop ≤ (rStar M μ : EReal) := by
  obtain ⟨hRA, hPf, hRPm, hstab, hpow⟩ := hadm
  have hRm : ∀ τ, Measurable (R τ) := fun τ => (hRPm τ).1
  have hPm : ∀ τ, Measurable (P τ) := fun τ => (hRPm τ).2
  have hSm : ∀ τ, Measurable (S τ) := fun τ => measurable_snd.comp (hAS τ)
  -- the per-slot quantities
  set Cq : ℕ → Ω → Fin L → ℝ := fun τ ω i => M.C i (P τ ω) (S τ ω) with hCq
  have hCm : ∀ τ i, Measurable (fun ω => Cq τ ω i) := fun τ i =>
    (hMm i).comp ((hPm τ).prodMk (hSm τ))
  have hCb : ∀ τ ω i, 0 ≤ Cq τ ω i ∧ Cq τ ω i ≤ M.muMax := fun τ ω i =>
    ⟨hM.rate_nonneg _ (hPf τ ω) _ i, hM.rate_le _ (hPf τ ω) _ i⟩
  have hRb : ∀ τ ω i, 0 ≤ R τ ω i ∧ R τ ω i ≤ M.Rhat := fun τ ω i =>
    ⟨(hRA τ ω i).1, (hRA τ ω i).2.trans (hA τ ω i).2⟩
  have hPb : ∀ τ ω, 0 ≤ ∑ i, P τ ω i ∧ ∑ i, P τ ω i ≤ M.Pmax := fun τ ω =>
    ⟨Finset.sum_nonneg fun i _ => (hPf τ ω).1 i, (hPf τ ω).2⟩
  have hRmi : ∀ τ i, Measurable (fun ω => R τ ω i) := fun τ i => (measurable_pi_apply i).comp (hRm τ)
  have hPsm : ∀ τ, Measurable (fun ω => ∑ i, P τ ω i) := fun τ =>
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp (hPm τ)
  have hRi : ∀ τ i, Integrable (fun ω => R τ ω i) Pr := fun τ i =>
    integrable_of_bdd Pr _ (hRmi τ i) M.Rhat fun ω => abs_le.mpr
      ⟨by linarith [(hRb τ ω i).1, hM.Rhat_nonneg], (hRb τ ω i).2⟩
  have hCi : ∀ τ i, Integrable (fun ω => Cq τ ω i) Pr := fun τ i =>
    integrable_of_bdd Pr _ (hCm τ i) M.muMax fun ω => abs_le.mpr
      ⟨by linarith [(hCb τ ω i).1, (hCb τ ω i).2], (hCb τ ω i).2⟩
  have hPi : ∀ τ, Integrable (fun ω => ∑ i, P τ ω i) Pr := fun τ =>
    integrable_of_bdd Pr _ (hPsm τ) M.Pmax fun ω => abs_le.mpr
      ⟨by linarith [(hPb τ ω).1, (hPb τ ω).2], (hPb τ ω).2⟩
  -- the time-averaged triple
  set q : ℕ → (Fin L → ℝ) × (Fin L → ℝ) × ℝ := fun t =>
    (fun i => (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, R τ ω i ∂Pr,
     fun i => (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, Cq τ ω i ∂Pr,
     (t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, ∑ i, P τ ω i ∂Pr) with hqdef
  -- membership in the achievable set
  set X : ℕ → Ω → ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) :=
    fun τ ω => ((A τ ω, S τ ω), (R τ ω, P τ ω)) with hXdef
  have hXm : ∀ τ, Measurable (X τ) := fun τ => (hAS τ).prodMk ((hRm τ).prodMk (hPm τ))
  have hmem : ∀ t, 1 ≤ t → q t ∈ achievable M μ := by
    intro t ht
    have ht0 : t ≠ 0 := by omega
    set ν := (t : ℝ≥0∞)⁻¹ • ∑ τ ∈ Finset.range t, Pr.map (X τ) with hν
    have happ : ∀ E, MeasurableSet E → ν E = (t : ℝ≥0∞)⁻¹ * ∑ τ ∈ Finset.range t, Pr (X τ ⁻¹' E) := by
      intro E hE
      rw [hν, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
      congr 1
      exact Finset.sum_congr rfl fun τ _ => Measure.map_apply (hXm τ) hE
    have htt : (t : ℝ≥0∞)⁻¹ * t = 1 :=
      ENNReal.inv_mul_cancel (by exact_mod_cast ht0) (ENNReal.natCast_ne_top t)
    have hmarg : ν.map Prod.fst = μ := by
      ext E hE
      rw [Measure.map_apply measurable_fst hE, happ _ (measurable_fst hE)]
      have : ∀ τ, Pr (X τ ⁻¹' (Prod.fst ⁻¹' E)) = μ E := by
        intro τ
        rw [← hlaw τ, Measure.map_apply (hAS τ) hE]
        rfl
      simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, htt, one_mul]
    have hμ1 : μ Set.univ = 1 := by
      rw [← hlaw 0, Measure.map_apply (hAS 0) MeasurableSet.univ]; simp
    have hprob : IsProbabilityMeasure ν := by
      constructor
      have := congrArg (fun m : Measure _ => m Set.univ) hmarg
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at this
      rw [this, hμ1]
    have hgoodm : MeasurableSet {x : ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) |
        (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2} := by
      simp only [IsFeasiblePower, Set.setOf_and, Set.setOf_forall]
      refine MeasurableSet.inter (MeasurableSet.iInter fun i =>
        (measurableSet_le measurable_const (by fun_prop)).inter
          (measurableSet_le (by fun_prop) (by fun_prop)))
        ((MeasurableSet.iInter fun i => measurableSet_le measurable_const (by fun_prop)).inter
          (measurableSet_le (by fun_prop) measurable_const))
    have hae : ∀ᵐ x ∂ν, (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2 := by
      rw [ae_iff, ← Set.compl_setOf, happ _ hgoodm.compl]
      have : ∀ τ, Pr (X τ ⁻¹' {x : ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) |
          (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2}ᶜ) = 0 := by
        intro τ
        have : X τ ⁻¹' {x : ((Fin L → ℝ) × 𝒮) × ((Fin L → ℝ) × (Fin L → ℝ)) |
            (∀ i, 0 ≤ x.2.1 i ∧ x.2.1 i ≤ x.1.1 i) ∧ IsFeasiblePower M x.2.2}ᶜ = ∅ := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
            Set.mem_empty_iff_false, iff_false, not_not]
          exact ⟨fun i => hRA τ ω i, hPf τ ω⟩
        rw [this, measure_empty]
      rw [Finset.sum_congr rfl (fun τ _ => this τ)]
      simp
    have mR := fun i => avg_integral Pr X hXm t ht0 (fun x => x.2.1 i) (by fun_prop)
      (fun τ => hRi τ i)
    have mC := fun i => avg_integral Pr X hXm t ht0 (fun x => M.C i x.2.2 x.1.2)
      ((hMm i).comp ((measurable_snd.comp measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))) (fun τ => hCi τ i)
    have mP := avg_integral Pr X hXm t ht0 (fun x => ∑ i, x.2.2 i) (by fun_prop) hPi
    refine ⟨ν, hprob, hmarg, hae, fun i => ⟨(mR i).1, (mC i).1⟩, ?_⟩
    simp only [hqdef]
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) ?_)
    · exact ((mR i).2).symm
    · exact ((mC i).2).symm
    · exact mP.2.symm
  -- the triples lie in a box
  have hbox : ∀ t, 1 ≤ t → q t ∈ Set.Icc (0 : (Fin L → ℝ) × (Fin L → ℝ) × ℝ)
      (fun _ => M.Rhat, fun _ => M.muMax, M.Pmax) := by
    intro t ht
    have bR := fun i => avg_bounds Pr (fun τ ω => R τ ω i) (fun τ => hRi τ i) 0 M.Rhat
      (fun τ ω => hRb τ ω i) t ht
    have bC := fun i => avg_bounds Pr (fun τ ω => Cq τ ω i) (fun τ => hCi τ i) 0 M.muMax
      (fun τ ω => hCb τ ω i) t ht
    have bP := avg_bounds Pr (fun τ ω => ∑ i, P τ ω i) hPi 0 M.Pmax hPb t ht
    exact ⟨⟨fun i => (bR i).1, fun i => (bC i).1, bP.1⟩, ⟨fun i => (bR i).2, fun i => (bC i).2, bP.2⟩⟩
  -- throughput is the first component
  have hthr : ∀ t, throughputAvg Pr R t = ∑ i, (q t).1 i := by
    intro t
    simp only [throughputAvg, hqdef, ← Finset.mul_sum]
    rw [Finset.sum_comm]
  -- the stability gap
  have hgapall : ∀ i, ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ t, 1 ≤ t → (q t).1 i - (q t).2.1 i ≤ e t := by
    intro i
    set Uq : Ω → ℕ → ℝ := fun ω t =>
      queueU M u₀ (fun τ => S τ ω) (fun τ => R τ ω) (fun τ => P τ ω) t i with hUq
    have hUstep : ∀ ω t, Uq ω (t + 1) = max (Uq ω t - Cq t ω i) 0 + R t ω i := fun ω t => rfl
    have hU0 : ∀ ω, Uq ω 0 = u₀ i := fun ω => rfl
    have hUm : ∀ t, Measurable (fun ω => Uq ω t) := by
      intro t
      induction t with
      | zero => simp only [hU0]; exact measurable_const
      | succ t ih =>
        simp only [hUstep]
        exact ((ih.sub (hCm t i)).max measurable_const).add (hRmi t i)
    have hUb : ∀ ω t, |Uq ω t| ≤ |u₀ i| + t * M.Rhat := by
      intro ω t
      induction t with
      | zero => simp [hU0]
      | succ t ih =>
        rw [hUstep]
        have h1 := (hCb t ω i).1
        have h2 := hRb t ω i
        have h3 := le_max_right (Uq ω t - Cq t ω i) 0
        have h4 : max (Uq ω t - Cq t ω i) 0 ≤ |Uq ω t| :=
          max_le (by linarith [le_abs_self (Uq ω t)]) (abs_nonneg _)
        have h5 := abs_nonneg (u₀ i)
        rw [abs_le]
        push_cast
        constructor <;> nlinarith [hM.Rhat_nonneg]
    have hUi : ∀ t, Integrable (fun ω => Uq ω t) Pr := fun t =>
      integrable_of_bdd Pr _ (hUm t) _ fun ω => hUb ω t
    have hUlow : ∀ ω t, u₀ i + ∑ τ ∈ Finset.range t, (R τ ω i - Cq τ ω i) ≤ Uq ω t := by
      intro ω t
      induction t with
      | zero => simp [hU0]
      | succ t ih =>
        rw [hUstep, Finset.sum_range_succ]
        have := le_max_left (Uq ω t - Cq t ω i) 0
        linarith
    refine ⟨fun t => (t : ℝ)⁻¹ * ((∫ ω, Uq ω t ∂Pr) - u₀ i), ?_, ?_⟩
    · have h1 := hstab i
      have h2 := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (u₀ i)
      have h3 := h1.sub h2
      simp only [mul_zero, sub_zero] at h3
      refine h3.congr fun t => ?_
      simp only [Function.comp, hUq]
      ring
    · intro t ht
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht
      simp only [hqdef]
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Finset.sum_sub_distrib]
      have e1 : ∑ τ ∈ Finset.range t, ((∫ ω, R τ ω i ∂Pr) - ∫ ω, Cq τ ω i ∂Pr) =
          ∫ ω, ∑ τ ∈ Finset.range t, (R τ ω i - Cq τ ω i) ∂Pr := by
        have hI : ∀ τ ∈ Finset.range t, Integrable (fun ω => R τ ω i - Cq τ ω i) Pr :=
          fun τ _ => (hRi τ i).sub (hCi τ i)
        rw [integral_finset_sum _ hI]
        exact Finset.sum_congr rfl fun τ _ => (integral_sub (hRi τ i) (hCi τ i)).symm
      rw [e1]
      have e2 : (∫ ω, Uq ω t ∂Pr) - u₀ i = ∫ ω, (Uq ω t - u₀ i) ∂Pr := by
        rw [integral_sub (hUi t) (integrable_const _)]; simp
      rw [e2]
      have hI : ∀ τ ∈ Finset.range t, Integrable (fun ω => R τ ω i - Cq τ ω i) Pr :=
        fun τ _ => (hRi τ i).sub (hCi τ i)
      refine integral_mono (integrable_finset_sum _ hI) ((hUi t).sub (integrable_const _)) ?_
      intro ω
      have := hUlow ω t
      simp only [Finset.sum_apply, Pi.sub_apply]
      linarith
  -- the set defining rStar is bounded above
  set Sset := {y : ℝ | ∃ q ∈ closure (achievable M μ),
    (∀ i, q.1 i ≤ q.2.1 i) ∧ q.2.2 ≤ M.Pav ∧ y = ∑ i, q.1 i} with hSset
  have hrs : rStar M μ = sSup Sset := rfl
  have hbdd : BddAbove Sset := by
    have hK : achievable M μ ⊆ {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ | ∀ i, q.1 i ≤ M.Rhat} := by
      rintro _ ⟨ν, hν, hmarg, hae, hint, rfl⟩ i
      have hmu : ∀ᵐ p ∂μ, p.1 i ≤ M.Rhat := by
        have hset : MeasurableSet {p : (Fin L → ℝ) × 𝒮 | ¬ p.1 i ≤ M.Rhat} :=
          (measurableSet_le ((measurable_pi_apply i).comp measurable_fst) measurable_const).compl
        rw [ae_iff, ← hlaw 0, Measure.map_apply (hAS 0) hset]
        have : (fun ω => (A 0 ω, S 0 ω)) ⁻¹' {p : (Fin L → ℝ) × 𝒮 | ¬ p.1 i ≤ M.Rhat} = ∅ := by
          ext ω; simp [(hA 0 ω i).2]
        rw [this, measure_empty]
      rw [← hmarg] at hmu
      have hnu := ae_of_ae_map measurable_fst.aemeasurable hmu
      show ∫ x, x.2.1 i ∂ν ≤ M.Rhat
      have := integral_mono_ae (hint i).1 (integrable_const M.Rhat)
        (by filter_upwards [hae, hnu] with x hx hx'; exact (hx.1 i).2.trans hx')
      simpa using this
    have hKc : IsClosed {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ | ∀ i, q.1 i ≤ M.Rhat} := by
      have : {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ | ∀ i, q.1 i ≤ M.Rhat} =
          ⋂ i, {q : (Fin L → ℝ) × (Fin L → ℝ) × ℝ | q.1 i ≤ M.Rhat} := by ext; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
    refine ⟨∑ _i : Fin L, M.Rhat, ?_⟩
    rintro y ⟨q', hq', -, -, rfl⟩
    exact Finset.sum_le_sum fun i _ => closure_minimal hK hKc hq' i
  -- main argument
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hz1' : rStar M μ < z := EReal.coe_lt_coe_iff.mp hz1
  have hfreq : ∃ᶠ t in atTop, (z : EReal) < (throughputAvg Pr R t : EReal) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hz2
  have hfreq' : ∃ᶠ t in atTop, z < throughputAvg Pr R t ∧ 1 ≤ t :=
    (hfreq.mono fun t ht => EReal.coe_lt_coe_iff.mp ht).and_eventually (eventually_ge_atTop 1)
  obtain ⟨φ, hφm, hφ⟩ := extraction_of_frequently_atTop hfreq'
  obtain ⟨qs, -, ψ, hψm, hψ⟩ := (isCompact_Icc (a := (0 : (Fin L → ℝ) × (Fin L → ℝ) × ℝ))
    (b := (fun _ => M.Rhat, fun _ => M.muMax, M.Pmax))).tendsto_subseq
    (x := fun n => q (φ n)) (fun n => hbox (φ n) (hφ n).2)
  have hφψ : Tendsto (fun k => φ (ψ k)) atTop atTop := (hφm.comp hψm).tendsto_atTop
  have hqcl : qs ∈ closure (achievable M μ) :=
    mem_closure_of_tendsto hψ (Eventually.of_forall fun k => hmem _ (hφ (ψ k)).2)
  have hq1 : ∀ i, qs.1 i ≤ qs.2.1 i := by
    intro i
    obtain ⟨e, he, hge⟩ := hgapall i
    have hc : Continuous (fun x : (Fin L → ℝ) × (Fin L → ℝ) × ℝ => x.1 i - x.2.1 i) := by
      fun_prop
    have := le_of_tendsto_of_tendsto' ((hc.tendsto qs).comp hψ) (he.comp hφψ)
      (fun k => hge _ (hφ (ψ k)).2)
    linarith
  have hq2 : qs.2.2 ≤ M.Pav := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hlt' : limsup (fun t : ℕ =>
        (((t : ℝ)⁻¹ * ∑ τ ∈ Finset.range t, ∫ ω, ∑ i, P τ ω i ∂Pr : ℝ) : EReal)) atTop <
        ((M.Pav + ε : ℝ) : EReal) :=
      hpow.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
    have hev := (eventually_lt_of_limsup_lt hlt').mono fun t ht => (EReal.coe_lt_coe_iff.mp ht).le
    have hc : Continuous (fun x : (Fin L → ℝ) × (Fin L → ℝ) × ℝ => x.2.2) := by fun_prop
    exact le_of_tendsto ((hc.tendsto qs).comp hψ) (hφψ.eventually hev)
  have hsum : z ≤ ∑ i, qs.1 i := by
    have hc : Continuous (fun x : (Fin L → ℝ) × (Fin L → ℝ) × ℝ => ∑ i, x.1 i) := by fun_prop
    refine ge_of_tendsto ((hc.tendsto qs).comp hψ) (Eventually.of_forall fun k => ?_)
    have := (hφ (ψ k)).1
    rw [hthr] at this
    exact this.le
  have hle : ∑ i, qs.1 i ≤ rStar M μ := by
    rw [hrs]; exact le_csSup hbdd ⟨qs, hqcl, hq1, hq2, rfl⟩
  linarith
