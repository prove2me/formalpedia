-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T18:22:55.987178+00:00
-- url     : https://prove2.me/submissions/7b51e4a9-927f-4c22-8da4-8ba92584ab0f

import Mathlib
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model


open scoped BigOperators

namespace Utility7.FairProof

lemma product_failure_le_exp {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq : ∀ k ∈ s, 0 ≤ q k ∧ q k ≤ 1) :
    (∏ k ∈ s, (1 - q k)) ≤ Real.exp (-(∑ k ∈ s, q k)) := by
  calc
    _ ≤ ∏ k ∈ s, Real.exp (-q k) := by
      apply Finset.prod_le_prod
      · intro k hk
        linarith [(hq k hk).2]
      · intro k hk
        have h := Real.add_one_le_exp (-q k)
        linarith
    _ = Real.exp (-(∑ k ∈ s, q k)) := by
      rw [← Real.exp_sum]
      congr 1
      simp

lemma exponential_chord {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (-s) ≤ 1 - (1 - Real.exp (-1)) * s := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (show 0 ≤ 1 - s by linarith) hs (show 1 - s + s = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_neg, mul_one, Real.exp_zero] at h
  nlinarith

lemma selection_lower_bound {α : Type*} [DecidableEq α] (s : Finset α) (q : α → ℝ)
    (hq : ∀ k ∈ s, 0 ≤ q k ∧ q k ≤ 1)
    (hs : ∑ k ∈ s, q k ≤ 1) (hpos : 0 < ∑ k ∈ s, q k) :
    1 - Real.exp (-1) ≤ (1 - ∏ k ∈ s, (1 - q k)) / ∑ k ∈ s, q k := by
  apply (le_div_iff₀ hpos).mpr
  have hprod := product_failure_le_exp s q hq
  have hchord := exponential_chord (le_of_lt hpos) hs
  linarith

end Utility7.FairProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Utility7.SurplusProof

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def maximum (f : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => f i ω)

lemma maximum_nonneg (f : ι → Ω → ℝ) (hf : ∀ i ω, 0 ≤ f i ω) (ω : Ω) :
    0 ≤ maximum f ω := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (hf i ω).trans (Finset.le_sup' (fun i => f i ω) (Finset.mem_univ i))

lemma maximum_integrable (f : ι → Ω → ℝ) (hm : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (f i) μ) (hn : ∀ i ω, 0 ≤ f i ω) :
    Integrable (maximum f) μ := by
  have hsum : Integrable (fun ω => ∑ i, f i ω) μ := integrable_finset_sum _ (fun i _ => hi i)
  have hmeas : Measurable (maximum f) := by
    have he : maximum f = Finset.univ.sup' Finset.univ_nonempty f := by
      funext ω
      exact (Finset.sup'_apply Finset.univ_nonempty f ω).symm
    rw [he]
    exact Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hm i)
  apply hsum.mono' hmeas.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (maximum_nonneg f hn ω)]
  apply Finset.sup'_le
  intro i hi
  exact Finset.single_le_sum (fun j _ => hn j ω) (Finset.mem_univ i)

lemma tail_integrable (f : Ω → ℝ) (hi : Integrable f μ) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable (fun t : ℝ => μ.real {ω | t < f ω}) (volume.restrict (Ioi 0)) := by
  apply integrable_toReal_of_lintegral_ne_top
  · apply Measurable.aemeasurable
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (fun ω h => lt_of_le_of_lt hab h)
  · rw [← lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hn) hi.aemeasurable]
    exact hi.lintegral_lt_top.ne

lemma maximum_tail (f : ι → Ω → ℝ) (hm : ∀ i, Measurable (f i))
    (hind : iIndepFun f μ) (t : ℝ) :
    μ.real {ω | t < maximum f ω} = 1 - ∏ i, (1 - μ.real {ω | t < f i ω}) := by
  have hset : {ω | t < maximum f ω} = (⋂ i, f i ⁻¹' Iic t)ᶜ := by
    ext ω
    simp only [mem_setOf_eq, mem_compl_iff, mem_iInter, mem_preimage, mem_Iic]
    change (t < Finset.univ.sup' Finset.univ_nonempty (fun i => f i ω)) ↔ _
    rw [← not_le, Finset.sup'_le_iff]
    simp
  have hinter := hind.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ => Iic t) (fun _ _ => measurableSet_Iic)
  simp only [Finset.mem_univ, iInter_true] at hinter
  have hinterR := congrArg ENNReal.toReal hinter
  rw [ENNReal.toReal_prod] at hinterR
  have hcomp (i : ι) : (μ (f i ⁻¹' Iic t)).toReal = 1 - μ.real {ω | t < f i ω} := by
    have hci : f i ⁻¹' Iic t = {ω | t < f i ω}ᶜ := by ext ω; simp
    rw [hci]
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using
      (measureReal_compl (measurableSet_lt measurable_const (hm i)) (μ := μ))
  rw [hset]
  have hms : MeasurableSet (⋂ i, f i ⁻¹' Iic t) :=
    MeasurableSet.iInter (fun i => (hm i) measurableSet_Iic)
  rw [measureReal_compl hms, probReal_univ]
  rw [show μ.real (⋂ i, f i ⁻¹' Iic t) = ∏ i, (1 - μ.real {ω | t < f i ω}) by
    change (μ (⋂ i, f i ⁻¹' Iic t)).toReal = _
    rw [hinterR]
    exact Finset.prod_congr rfl (fun i _ => hcomp i)]

lemma independent_maximum_bound (f : ι → Ω → ℝ) (hm : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (f i) μ) (hn : ∀ i ω, 0 ≤ f i ω)
    (hind : iIndepFun f μ) (hcap : ∑ i, μ.real {ω | 0 < f i ω} ≤ 1) :
    (1 - Real.exp (-1)) * ∑ i, (∫ ω, f i ω ∂μ) ≤ ∫ ω, maximum f ω ∂μ := by
  have hmax := maximum_integrable f hm hi hn
  have ht (i : ι) := tail_integrable (f i) (hi i) (hn i)
  have htailmax := tail_integrable (maximum f) hmax (maximum_nonneg f hn)
  have hpoint (t : ℝ) (ht : 0 < t) :
      (1 - Real.exp (-1)) * ∑ i, μ.real {ω | t < f i ω} ≤ μ.real {ω | t < maximum f ω} := by
    let q : ι → ℝ := fun i => μ.real {ω | t < f i ω}
    have hq (i : ι) : 0 ≤ q i ∧ q i ≤ 1 := ⟨measureReal_nonneg,
      (measureReal_mono (subset_univ _)).trans_eq probReal_univ⟩
    have hsum : ∑ i, q i ≤ 1 := by
      apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hcap
      exact measureReal_mono (fun ω h => ht.trans h)
    rw [maximum_tail f hm hind t]
    have hp := FairProof.product_failure_le_exp Finset.univ q (fun i _ => hq i)
    have hc := FairProof.exponential_chord (Finset.sum_nonneg (fun i _ => (hq i).1)) hsum
    change (1 - Real.exp (-1)) * ∑ i, q i ≤ 1 - ∏ i, (1 - q i)
    linarith
  calc
    _ = (1 - Real.exp (-1)) * ∑ i,
        (∫ t in Ioi (0 : ℝ), μ.real {ω | t < f i ω}) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hi i).integral_eq_integral_meas_lt (Filter.Eventually.of_forall (hn i))
    _ = ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-1)) * ∑ i, μ.real {ω | t < f i ω} := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ => ht i)]
    _ ≤ ∫ t in Ioi (0 : ℝ), μ.real {ω | t < maximum f ω} := by
      apply integral_mono_ae ((integrable_finset_sum _ (fun i _ => ht i)).const_mul _) htailmax
      exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun t ht => hpoint t ht))
    _ = _ := (hmax.integral_eq_integral_meas_lt
      (Filter.Eventually.of_forall (maximum_nonneg f hn))).symm

end Utility7.SurplusProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.SurplusProof

lemma surplus_nonneg (v : ℝ≥0) (t : ℝ≥0∞) : 0 ≤ surplus v t := by
  unfold surplus
  split_ifs <;> positivity

lemma surplus_le_value (v : ℝ≥0) (t : ℝ≥0∞) : surplus v t ≤ v := by
  unfold surplus
  split_ifs
  · exact v.coe_nonneg
  · exact max_le (sub_le_self _ ENNReal.toReal_nonneg) v.coe_nonneg

lemma measurable_surplus : Measurable (fun z : ℝ≥0∞ × ℝ≥0 => surplus z.2 z.1) := by
  unfold surplus
  have hval : Measurable (fun z : ℝ≥0∞ × ℝ≥0 => (z.2 : ℝ)) := by fun_prop
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const ((hval.sub (ENNReal.measurable_toReal.comp measurable_fst)).max measurable_const)

lemma surplus_pos_iff (v : ℝ≥0) (t : ℝ≥0∞) :
    0 < surplus v t ↔ t < (v : ℝ≥0∞) := by
  by_cases ht : t = ⊤
  · simp [surplus, ht]
  · rw [surplus, if_neg ht, lt_max_iff]
    simp only [lt_self_iff_false, or_false, sub_pos]
    simpa using (ENNReal.toReal_lt_toReal ht (by simp : (v : ℝ≥0∞) ≠ ⊤))

lemma choice_mem {m : ℕ} (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) (j : Fin m)
    (hj : j ∈ udCandidates v t) :
    0 < surplus (v j) (t j) ∧ ∀ k, surplus (v k) (t k) ≤ surplus (v j) (t j) := by
  simpa only [udCandidates, Finset.mem_filter, Finset.mem_univ, true_and] using hj

lemma choice_bounds {m : ℕ} (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) (j : Fin m) :
    0 ≤ udChoice v t j ∧ udChoice v t j ≤ 1 := by
  unfold udChoice
  split_ifs with hj
  · have hcard : 1 ≤ ((udCandidates v t).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr ⟨j, hj⟩)
    constructor
    · positivity
    · exact (div_le_one (by linarith)).mpr hcard
  · simp

lemma choice_le_sale {m : ℕ} (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) (j : Fin m) :
    udChoice v t j ≤ if t j < (v j : ℝ≥0∞) then 1 else 0 := by
  by_cases hj : j ∈ udCandidates v t
  · rw [if_pos ((surplus_pos_iff _ _).mp (choice_mem v t j hj).1)]
    exact (choice_bounds v t j).2
  · simp only [udChoice, if_neg hj]
    split_ifs <;> norm_num

lemma choice_utility_maximum {m : ℕ} [Nonempty (Fin m)]
    (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) :
    (∑ j, udChoice v t j * surplus (v j) (t j)) =
      maximum (fun j (_ : Unit) => surplus (v j) (t j)) () := by
  let M := maximum (fun j (_ : Unit) => surplus (v j) (t j)) ()
  have hnon : 0 ≤ M := maximum_nonneg _ (fun j _ => surplus_nonneg _ _) ()
  have hle (j : Fin m) : surplus (v j) (t j) ≤ M := by
    change surplus (v j) (t j) ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun j => surplus (v j) (t j))
    exact Finset.le_sup' (fun j => surplus (v j) (t j)) (Finset.mem_univ j)
  by_cases hpos : 0 < M
  · obtain ⟨j, hj, hjM⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun j => surplus (v j) (t j))
    have hjc : j ∈ udCandidates v t := by
      simp only [udCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hjM ▸ hpos
      · intro k
        exact hjM ▸ hle k
    have hcard : ((udCandidates v t).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr ⟨j, hjc⟩)
    calc
      _ = ∑ j ∈ udCandidates v t, (1 / ((udCandidates v t).card : ℝ)) * M := by
        simp only [udChoice, ite_mul, zero_mul]
        rw [← Finset.sum_filter]
        simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : surplus (v k) (t k) = M := le_antisymm (hle k) (by
          change Finset.univ.sup' Finset.univ_nonempty (fun j => surplus (v j) (t j)) ≤ _
          exact Finset.sup'_le _ _ (fun j _ => (choice_mem v t k hk).2 j))
        rw [hkm]
      _ = M := by simp [hcard, mul_assoc]
  · have hM : M = 0 := le_antisymm (le_of_not_gt hpos) hnon
    have hz (j : Fin m) : surplus (v j) (t j) = 0 :=
      le_antisymm ((hle j).trans_eq hM) (surplus_nonneg _ _)
    change (∑ j, udChoice v t j * surplus (v j) (t j)) = M
    simp only [hz, mul_zero, Finset.sum_const_zero]
    exact hM.symm

end Utility7.SurplusProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.SurplusProof

lemma surplus_integrable (ν : ProbabilityMeasure ℝ≥0) (π : Measure ℝ≥0∞)
    [IsProbabilityMeasure π] (hν : HasFiniteMean ν) :
    Integrable (fun z : ℝ≥0∞ × ℝ≥0 => surplus z.2 z.1) (π.prod (ν : Measure ℝ≥0)) := by
  apply (hν.comp_snd π).mono' measurable_surplus.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (surplus_nonneg _ _)]
  exact surplus_le_value _ _

lemma sale_integral (ν : ProbabilityMeasure ℝ≥0) (π : Measure ℝ≥0∞)
    [IsProbabilityMeasure π] :
    (π.prod (ν : Measure ℝ≥0)).real {z | 0 < surplus z.2 z.1} = saleProb1 ν π := by
  have he : {z : ℝ≥0∞ × ℝ≥0 | 0 < surplus z.2 z.1} = {z | z.1 < (z.2 : ℝ≥0∞)} := by
    ext z
    exact surplus_pos_iff _ _
  have hm : MeasurableSet {z : ℝ≥0∞ × ℝ≥0 | z.1 < (z.2 : ℝ≥0∞)} := by
    apply measurableSet_lt measurable_fst
    fun_prop
  have hint : Integrable (fun z : ℝ≥0∞ × ℝ≥0 =>
      if z.1 < (z.2 : ℝ≥0∞) then (1 : ℝ) else 0) (π.prod (ν : Measure ℝ≥0)) :=
    by
      have hI : Integrable ({z : ℝ≥0∞ × ℝ≥0 | z.1 < (z.2 : ℝ≥0∞)}.indicator
          (fun _ => (1 : ℝ))) (π.prod (ν : Measure ℝ≥0)) :=
        (integrable_const (1 : ℝ)).indicator hm
      apply hI.congr
      apply Filter.Eventually.of_forall
      intro z
      simp [Set.indicator]
  rw [he]
  calc
    _ = ∫ z, if z.1 < (z.2 : ℝ≥0∞) then (1 : ℝ) else 0 ∂(π.prod (ν : Measure ℝ≥0)) := by
      simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul,
        one_mul, mul_one] using (integral_indicator_one hm).symm
    _ = _ := by
      rw [integral_prod _ hint]
      unfold saleProb1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      have hmt : MeasurableSet {v : ℝ≥0 | t < (v : ℝ≥0∞)} := by
        apply measurableSet_lt measurable_const
        fun_prop
      simpa only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, Measure.real] using
        (integral_indicator_one (μ := (ν : Measure ℝ≥0)) hmt)

lemma joint_surplus_integral (ν : ProbabilityMeasure ℝ≥0) (π : Measure ℝ≥0∞)
    [IsProbabilityMeasure π] (hν : HasFiniteMean ν) :
    (∫ z : ℝ≥0∞ × ℝ≥0, surplus z.2 z.1 ∂(π.prod (ν : Measure ℝ≥0))) = postedUtility1 ν π :=
  integral_prod _ (surplus_integrable ν π hν)

end Utility7.SurplusProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.SurplusProof

abbrev PriceValue := ℝ≥0∞ × ℝ≥0

noncomputable def jointLaw {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) : Measure (Fin m → PriceValue) :=
  Measure.pi (fun j => (π j).prod (G j : Measure ℝ≥0))

instance jointLaw_prob {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] :
    IsProbabilityMeasure (jointLaw G π) := by unfold jointLaw; infer_instance

noncomputable def jointSurplus {m : ℕ} (j : Fin m) (z : Fin m → PriceValue) : ℝ :=
  surplus (z j).2 (z j).1

lemma jointSurplus_measurable {m : ℕ} (j : Fin m) : Measurable (jointSurplus j) :=
  measurable_surplus.comp (measurable_pi_apply j)

lemma jointSurplus_integrable {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)]
    (hG : ∀ j, HasFiniteMean (G j)) (j : Fin m) :
    Integrable (jointSurplus j) (jointLaw G π) := by
  change Integrable (fun z : Fin m → PriceValue => surplus (z j).2 (z j).1)
    (Measure.pi (fun j => (π j).prod (G j : Measure ℝ≥0)))
  exact integrable_comp_eval (μ := fun j => (π j).prod (G j : Measure ℝ≥0))
    (i := j) (surplus_integrable (G j) (π j) (hG j))

lemma jointSurplus_mean {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)]
    (hG : ∀ j, HasFiniteMean (G j)) (j : Fin m) :
    (∫ z, jointSurplus j z ∂jointLaw G π) = postedUtility1 (G j) (π j) := by
  unfold jointLaw jointSurplus
  calc
    _ = ∫ z : PriceValue, surplus z.2 z.1 ∂((π j).prod (G j : Measure ℝ≥0)) :=
      integral_comp_eval (μ := fun j => (π j).prod (G j : Measure ℝ≥0)) (i := j)
        (surplus_integrable (G j) (π j) (hG j)).aestronglyMeasurable
    _ = _ := joint_surplus_integral (G j) (π j) (hG j)

lemma jointSurplus_sale {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] (j : Fin m) :
    (jointLaw G π).real {z | 0 < jointSurplus j z} = saleProb1 (G j) (π j) := by
  have hset : {z | 0 < jointSurplus j z} =
      (Function.eval j) ⁻¹' {z : PriceValue | 0 < surplus z.2 z.1} := rfl
  have hms : MeasurableSet {z : PriceValue | 0 < surplus z.2 z.1} :=
    measurableSet_lt measurable_const measurable_surplus
  rw [hset, Measure.real, jointLaw, (measurePreserving_eval
    (fun j => (π j).prod (G j : Measure ℝ≥0)) j).measure_preimage hms.nullMeasurableSet]
  exact sale_integral (G j) (π j)

lemma jointSurplus_independent {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] :
    iIndepFun (jointSurplus : Fin m → (Fin m → PriceValue) → ℝ) (jointLaw G π) :=
  iIndepFun_pi (fun _ => measurable_surplus.aemeasurable)

lemma joint_integrable_iff {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)]
    (F : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) → ℝ) :
    Integrable (fun z => F ((fun j => (z j).1), (fun j => (z j).2))) (jointLaw G π) ↔
      Integrable F ((Measure.pi π).prod (vecLaw G)) := by
  exact (measurePreserving_arrowProdEquivProdArrow ℝ≥0∞ ℝ≥0 (Fin m)
    π (fun j => (G j : Measure ℝ≥0))).integrable_comp_emb
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ≥0∞ ℝ≥0 (Fin m)).measurableEmbedding

/-- Regrouping independent pairs into the published nested price/value integrals. -/
lemma joint_integral_nested {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)]
    (F : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) → ℝ)
    (hF : Integrable F ((Measure.pi π).prod (vecLaw G))) :
    (∫ z, F ((fun j => (z j).1), (fun j => (z j).2)) ∂jointLaw G π) =
      ∫ t, ∫ v, F (t, v) ∂vecLaw G ∂Measure.pi π := by
  have hmp := measurePreserving_arrowProdEquivProdArrow ℝ≥0∞ ℝ≥0 (Fin m)
    π (fun j => (G j : Measure ℝ≥0))
  calc
    _ = ∫ z, F z ∂((Measure.pi π).prod (vecLaw G)) := hmp.integral_comp' F
    _ = _ := integral_prod F hF

end Utility7.SurplusProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.SurplusProof

lemma jointCandidates_measurable {m : ℕ} :
    Measurable (fun z : Fin m → PriceValue => udCandidates (fun j => (z j).2) (fun j => (z j).1)) := by
  apply measurable_finset_iff.mpr
  intro j
  apply measurableSet_setOfPred.mp
  simp only [udCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  have hm (k : Fin m) : Measurable (jointSurplus k) := jointSurplus_measurable k
  have ha : MeasurableSet {z : Fin m → PriceValue | ∀ k, jointSurplus k z ≤ jointSurplus j z} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le (hm k) (hm j))
  exact (measurableSet_lt measurable_const (hm j)).inter ha

lemma jointChoice_measurable {m : ℕ} (j : Fin m) :
    Measurable (fun z : Fin m → PriceValue => udChoice (fun j => (z j).2) (fun j => (z j).1) j) := by
  have hF : Measurable (fun S : Finset (Fin m) => if j ∈ S then 1 / (S.card : ℝ) else 0) :=
    measurable_of_countable _
  exact hF.comp jointCandidates_measurable

lemma jointChoice_integrable {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] (j : Fin m) :
    Integrable (fun z : Fin m → PriceValue => udChoice (fun j => (z j).2) (fun j => (z j).1) j)
      (jointLaw G π) := by
  apply (integrable_const (1 : ℝ)).mono' (jointChoice_measurable j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (choice_bounds _ _ j).1]
  exact (choice_bounds _ _ j).2

lemma allocation_joint {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] (j : Fin m) :
    udAlloc G π j = ∫ z, udChoice (fun j => (z j).2) (fun j => (z j).1) j ∂jointLaw G π := by
  exact (joint_integral_nested G π (fun z => udChoice z.2 z.1 j)
    ((joint_integrable_iff G π _).mp (jointChoice_integrable G π j))).symm

lemma allocation_le_sale {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) [∀ j, IsProbabilityMeasure (π j)] (j : Fin m) :
    udAlloc G π j ≤ saleProb1 (G j) (π j) := by
  have hm : MeasurableSet {z : Fin m → PriceValue | 0 < jointSurplus j z} :=
    measurableSet_lt measurable_const (jointSurplus_measurable j)
  have hint : Integrable ({z : Fin m → PriceValue | 0 < jointSurplus j z}.indicator (fun _ => (1 : ℝ)))
      (jointLaw G π) := (integrable_const (1 : ℝ)).indicator hm
  rw [allocation_joint]
  calc
    _ ≤ ∫ z, {z : Fin m → PriceValue | 0 < jointSurplus j z}.indicator (fun _ => (1 : ℝ)) z
        ∂jointLaw G π := by
      apply integral_mono (jointChoice_integrable G π j) hint
      intro z
      simpa only [Set.indicator, Set.mem_setOf_eq, jointSurplus, surplus_pos_iff] using
        choice_le_sale (fun j => (z j).2) (fun j => (z j).1) j
    _ = (jointLaw G π).real {z | 0 < jointSurplus j z} := integral_indicator_one hm
    _ = _ := jointSurplus_sale G π j

end Utility7.SurplusProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.SurplusProof

lemma utility_joint_maximum {m : ℕ} [Nonempty (Fin m)]
    (G : Fin m → ProbabilityMeasure ℝ≥0) (π : Fin m → Measure ℝ≥0∞)
    [∀ j, IsProbabilityMeasure (π j)] (hG : ∀ j, HasFiniteMean (G j)) :
    udUtility G π = ∫ z, maximum (jointSurplus : Fin m → (Fin m → PriceValue) → ℝ) z
      ∂jointLaw G π := by
  have hi := maximum_integrable (jointSurplus : Fin m → (Fin m → PriceValue) → ℝ)
    jointSurplus_measurable (jointSurplus_integrable G π hG)
    (fun j z => surplus_nonneg _ _)
  let F : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) → ℝ :=
    fun z => maximum (fun j (_ : Unit) => surplus (z.2 j) (z.1 j)) ()
  have hF : Integrable F ((Measure.pi π).prod (vecLaw G)) :=
    (joint_integrable_iff G π F).mp hi
  calc
    _ = ∫ t, ∫ v, F (t, v) ∂vecLaw G ∂Measure.pi π := by
      unfold udUtility
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
      exact choice_utility_maximum v t
    _ = _ := (joint_integral_nested G π F hF).symm

theorem lemma_3 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (π : Fin m → Measure ℝ≥0∞)
    [∀ j, IsProbabilityMeasure (π j)] (q : Fin m → ℝ)
    (hq : ∀ j, saleProb1 (G j) (π j) ≤ q j) (hsum : ∑ j, q j ≤ 1) :
    (∀ j, udAlloc G π j ≤ q j) ∧
      (1 - Real.exp (-1)) * ∑ j, postedUtility1 (G j) (π j) ≤ udUtility G π := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  constructor
  · intro j
    exact (allocation_le_sale G π j).trans (hq j)
  · rw [utility_joint_maximum G π (fun j => (hG j).1)]
    have hh := independent_maximum_bound (jointSurplus : Fin m → (Fin m → PriceValue) → ℝ)
      jointSurplus_measurable (jointSurplus_integrable G π (fun j => (hG j).1))
      (fun j z => surplus_nonneg _ _) (jointSurplus_independent G π) (μ := jointLaw G π)
    have hc : ∑ j, (jointLaw G π).real {z | 0 < jointSurplus j z} ≤ 1 := by
      apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hsum
      rw [jointSurplus_sale]
      exact hq j
    have hres := hh hc
    simpa only [jointSurplus_mean G π (fun j => (hG j).1)] using hres

end Utility7.SurplusProof

open ConsumerUtilityApprox.UnitDemand
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (π : Fin m → Measure ℝ≥0∞)
    [∀ j, IsProbabilityMeasure (π j)] (q : Fin m → ℝ)
    (hq : ∀ j, saleProb1 (G j) (π j) ≤ q j) (hsum : ∑ j, q j ≤ 1) :
    (∀ j, udAlloc G π j ≤ q j) ∧
      (1 - Real.exp (-1)) * ∑ j, postedUtility1 (G j) (π j) ≤ udUtility G π  := Utility7.SurplusProof.lemma_3 hm G hG π q hq hsum
