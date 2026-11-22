-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T09:18:48.772853+00:00
-- url     : https://prove2.me/submissions/85e29d8b-69cd-4e14-a654-3bf7129d7fb3

import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
import Mathlib
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Constructions.Pi


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma mean_nonnegative {α : Type} (p : PMF α) (f : α → ℝ)
    (hf : ∀ a ∈ p.support, 0 ≤ f a) :
    (∑' a, (p a).toReal * f a) = (∑' a, p a * ENNReal.ofReal (f a)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro a
  rw [ENNReal.toReal_mul]
  by_cases ha : p a = 0
  · simp [ha]
  · rw [ENNReal.toReal_ofReal (hf a (by simpa only [PMF.mem_support_iff] using ha))]

lemma ennreal_mean_map {α β : Type} (p : PMF α) (f : α → β) (g : β → ℝ≥0∞) :
    (∑' b, (p.map f) b * g b) = ∑' a, p a * g (f a) := by
  simp only [PMF.map_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  simp only [ite_mul, zero_mul, tsum_ite_eq]

/-- The literal real-valued PMF sum used in the public payment semantics
commutes with a pushforward for nonnegative supported payments. -/
lemma mean_map {α β : Type} (p : PMF α) (f : α → β) (g : β → ℝ)
    (hg : ∀ a ∈ p.support, 0 ≤ g (f a)) :
    (∑' b, ((p.map f) b).toReal * g b) = ∑' a, (p a).toReal * g (f a) := by
  have hg' : ∀ b ∈ (p.map f).support, 0 ≤ g b := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hb
    exact hg a ha
  rw [mean_nonnegative (p.map f) g hg', mean_nonnegative p (fun a => g (f a)) hg]
  rw [ennreal_mean_map]

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma ennreal_mean_le {α : Type} (p : PMF α) (g : α → ℝ) (B : ℝ)
    (hg : ∀ a ∈ p.support, g a ≤ B) :
    (∑' a, p a * ENNReal.ofReal (g a)) ≤ ENNReal.ofReal B := by
  calc
    _ ≤ ∑' a, p a * ENNReal.ofReal B := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : p a = 0
      · simp [ha]
      · exact mul_le_mul_of_nonneg_left
          (ENNReal.ofReal_le_ofReal (hg a ((p.mem_support_iff a).mpr ha))) (show 0 ≤ p a from bot_le)
    _ = _ := by rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

lemma ennreal_mean_bind {α β : Type} (p : PMF α) (q : α → PMF β) (g : β → ℝ≥0∞) :
    (∑' b, (p.bind q) b * g b) = ∑' a, p a * (∑' b, q a b * g b) := by
  simp only [PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

lemma mean_bind {α β : Type} (p : PMF α) (q : α → PMF β) (g : β → ℝ) (B : ℝ)
    (hg : ∀ a ∈ p.support, ∀ b ∈ (q a).support, 0 ≤ g b ∧ g b ≤ B) :
    (∑' b, ((p.bind q) b).toReal * g b) =
      ∑' a, (p a).toReal * (∑' b, (q a b).toReal * g b) := by
  have hnonneg : ∀ b ∈ (p.bind q).support, 0 ≤ g b := by
    intro b hb
    obtain ⟨a, ha, hb⟩ := (PMF.mem_support_bind_iff _ _ _).mp hb
    exact (hg a ha b hb).1
  have hfin (a : α) : p a * (∑' b, q a b * ENNReal.ofReal (g b)) ≠ ⊤ := by
    by_cases ha : p a = 0
    · simp [ha]
    · apply ENNReal.mul_ne_top (p.apply_ne_top a)
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
        (ennreal_mean_le (q a) g B (fun b hb => (hg a ((p.mem_support_iff a).mpr ha) b hb).2))
  rw [mean_nonnegative (p.bind q) g hnonneg, ennreal_mean_bind, ENNReal.tsum_toReal_eq hfin]
  apply tsum_congr
  intro a
  rw [ENNReal.toReal_mul]
  by_cases ha : p a = 0
  · simp [ha]
  · rw [← mean_nonnegative (q a) g (fun b hb =>
      (hg a ((p.mem_support_iff a).mpr ha) b hb).1)]

end Utility7.ContentionProof


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

namespace Utility7.ContentionProof

lemma indep_support_coordinate {α : Type} {n : ℕ} (p : Fin n → PMF α)
    (v : Fin n → α) (hv : v ∈ (indep n p).support) (i : Fin n) : v i ∈ (p i).support := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    unfold indep at hv
    obtain ⟨a, ha, hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
    obtain ⟨g, hg, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
    subst v
    induction i using Fin.cases with
    | zero => exact ha
    | succ i => exact ih _ _ hg i

lemma uniformOn_support {α : Type} (s : Finset α) (j : α)
    (hj : some j ∈ (ConsumerUtilityApprox.UnitDemand.uniformOn s).support) : j ∈ s := by
  unfold ConsumerUtilityApprox.UnitDemand.uniformOn at hj
  split_ifs at hj with hs
  · obtain ⟨a, ha, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hj
    have hae : a = j := Option.some.inj he
    subst a
    simpa only [PMF.support_uniformOfFinset, Finset.mem_coe] using ha
  · simpa using hj

lemma pricing_request_valid {m : ℕ} (pr : Fin m → TwoPointPrice)
    (v : Fin m → ℝ≥0) (j : Fin m) (p : ℝ)
    (hreq : some (j, p) ∈ (pricingRequest pr v).support) :
    0 ≤ p ∧ p ≤ v j := by
  unfold pricingRequest at hreq
  obtain ⟨t, ht, hreq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hreq
  obtain ⟨c, hc, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hreq
  cases c with
  | none => simp at he
  | some k =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hk := uniformOn_support _ k hc
    have hsur := (SurplusProof.choice_mem v t k hk).1
    have hlt := (SurplusProof.surplus_pos_iff _ _).mp hsur
    have hfinite : t k ≠ ⊤ := ne_top_of_lt hlt
    constructor
    · exact ENNReal.toReal_nonneg
    · exact le_of_lt (by
        simpa only [ENNReal.coe_toReal] using
          (ENNReal.toReal_lt_toReal hfinite (by simp : (v k : ℝ≥0∞) ≠ ⊤)).mpr hlt)

lemma lottery_request_valid {m : ℕ} (lot : Fin m → ℝ)
    (v : Fin m → ℝ≥0) (j : Fin m) (p : ℝ)
    (hreq : some (j, p) ∈ (lotteryRequest lot v).support) :
    0 ≤ p ∧ p ≤ v j := by
  unfold lotteryRequest at hreq
  obtain ⟨c, hc, hreq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hreq
  cases c with
  | none => simp at hreq
  | some k =>
    obtain ⟨b, hb, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hreq
    cases b with
    | false => simp at he
    | true =>
      simp only [if_true, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨le_rfl, (v k).coe_nonneg⟩

lemma request_valid {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (v : Fin m → ℝ≥0) (j : Fin m) (p : ℝ)
    (hreq : some (j, p) ∈ (D.request i v).support) : 0 ≤ p ∧ p ≤ v j := by
  unfold MechDescription.request at hreq
  split_ifs at hreq with hT
  · obtain ⟨part, hp, hreq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hreq
    cases part with
    | false => simp at hreq
    | true =>
      obtain ⟨t, ht, hreq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hreq
      obtain ⟨br, hb, hreq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hreq
      cases br with
      | false => exact lottery_request_valid _ _ _ _ hreq
      | true => exact pricing_request_valid _ _ _ _ hreq
  · simp at hreq

def servedOutcome {n m : ℕ} (req : Fin n → Request m) (sel : Fin m → Option (Fin n)) :
    Outcome n m :=
  (fun i => match req i with
    | some (j, _) => if sel j = some i then some j else none
    | none => none,
   fun i => match req i with
    | some (j, p) => if sel j = some i then p else 0
    | none => 0)

lemma law_support {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (ω : Outcome n m) (hω : ω ∈ (D.law v).support) :
    ∃ req sel, req ∈ (indep n (fun i => D.request i (v i))).support ∧
      ω = servedOutcome req sel := by
  unfold MechDescription.law at hω
  obtain ⟨req, hr, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
  obtain ⟨sel, hs, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
  exact ⟨req, sel, hr, he.symm⟩

lemma served_item_selected {n m : ℕ} (req : Fin n → Request m) (sel : Fin m → Option (Fin n))
    (i : Fin n) (j : Fin m) (h : (servedOutcome req sel).1 i = some j) : sel j = some i := by
  cases hreq : req i with
  | none => simp [servedOutcome, hreq] at h
  | some a =>
    obtain ⟨k, p⟩ := a
    simp only [servedOutcome, hreq] at h
    split_ifs at h with hs
    · have hk : k = j := Option.some.inj h
      exact hk ▸ hs

theorem matching_feasible {n m : ℕ} (D : MechDescription n m) : D.law.IsMatchingFeasible := by
  intro v ω hω i i' j hi hi'
  obtain ⟨req, sel, hr, rfl⟩ := law_support D v ω hω
  have hs := served_item_selected req sel i j hi
  have hs' := served_item_selected req sel i' j hi'
  exact Option.some.inj (hs.symm.trans hs')

theorem realized_ir_and_nonnegative {n m : ℕ} (D : MechDescription n m) :
    D.law.IsExPostIR ∧ D.law.HasNonnegPayments := by
  have hpoint (v : Profile n m) (ω : Outcome n m) (hω : ω ∈ (D.law v).support) (i : Fin n) :
      0 ≤ assignValue (v i) (ω.1 i) - ω.2 i ∧ 0 ≤ ω.2 i := by
    obtain ⟨req, sel, hr, rfl⟩ := law_support D v ω hω
    have hri := indep_support_coordinate _ _ hr i
    cases hreq : req i with
    | none => simp [servedOutcome, hreq, assignValue]
    | some a =>
      obtain ⟨j, p⟩ := a
      rw [hreq] at hri
      have hv := request_valid D i (v i) j p hri
      by_cases hs : sel j = some i
      · simp only [servedOutcome, hreq, hs, if_true, assignValue]
        exact ⟨sub_nonneg.mpr hv.2, hv.1⟩
      · simp [servedOutcome, hreq, hs, assignValue]
  constructor
  · intro v ω hω i
    exact (hpoint v ω hω i).1
  · intro v ω hω i
    exact (hpoint v ω hω i).2

end Utility7.ContentionProof


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset

theorem projection_sq_le (z c : ℝ) (hc0:0 ≤ c) (hc1:c ≤ 1) :
    (min 1 (max 0 z)-c)^2 ≤ (z-c)^2 := by
  by_cases hz0:z ≤ 0
  · rw [max_eq_left hz0,min_eq_right (by norm_num: (0:ℝ) ≤ 1)]
    nlinarith
  · have hz0':0 ≤ z := by linarith
    rw [max_eq_right hz0']
    by_cases hz1:1 ≤ z
    · rw [min_eq_left hz1]
      nlinarith
    · rw [min_eq_right (by linarith: z ≤ 1)]

theorem projection_mem (z : ℝ) : 0 ≤ min 1 (max 0 z) ∧ min 1 (max 0 z) ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem lam_mem {m T : ℕ} (lam : ℕ→Fin m→ℝ) (g : ℕ→Fin m→ℝ) (η : ℝ)
    (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+η*g t j))) :
    ∀t ≤ T,∀j,0 ≤ lam t j ∧ lam t j ≤ 1 := by
  intro t ht
  cases t with
  | zero => intro j;rw [h0];norm_num
  | succ t => intro j;rw [hu t (by omega) j];exact projection_mem _

lemma sum_range_telescope (T : ℕ) (D : ℕ→ℝ) :
    (∑t∈range T,(D t-D (t+1)))=D 0-D T := by
  induction T with
  | zero => simp
  | succ T ih => rw [sum_range_succ,ih];ring

/-- Euclidean projected-gradient regret, with explicit scalar gradients
and literal clipping. No mechanism-side utility claim is assumed here. -/
theorem projected_regret {m T : ℕ} (lam g : ℕ→Fin m→ℝ) (η : ℝ) (hη:0<η)
    (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+η*g t j)))
    (c : Fin m→ℝ) (hc0:∀j,0 ≤ c j) (hc1:∀j,c j ≤ 1) :
    2*η*(∑t∈range T,∑j,(c j-lam t j)*g t j)  ≤ 
      (m:ℝ)+η^2*(∑t∈range T,∑j,(g t j)^2) := by
  let D:=fun t=>∑j,(lam t j-c j)^2
  have hstep:∀t<T,2*η*(∑j,(c j-lam t j)*g t j)  ≤ 
      D t-D (t+1)+η^2*(∑j,(g t j)^2) := by
    intro t ht
    have heach:∀j,2*η*((c j-lam t j)*g t j)  ≤ 
        (lam t j-c j)^2-(lam (t+1) j-c j)^2+η^2*(g t j)^2 := by
      intro j
      have hh:=projection_sq_le (lam t j+η*g t j) (c j) (hc0 j) (hc1 j)
      rw [← hu t ht j] at hh
      nlinarith
    have hs:=sum_le_sum (fun j (_:j∈(univ:Finset (Fin m)))=>heach j)
    simpa only [mul_sum,sum_add_distrib,sum_sub_distrib,D] using hs
  have hs:=sum_le_sum (fun t (ht:t∈range T)=>hstep t (mem_range.mp ht))
  rw [← mul_sum,sum_add_distrib,sum_range_telescope,← mul_sum] at hs
  have hD0:D 0  ≤  (m:ℝ) := by
    dsimp only [D]
    simp only [h0,zero_sub,neg_sq]
    calc
      _  ≤  ∑j:Fin m,(1:ℝ) := sum_le_sum (fun j _=>by nlinarith [hc0 j,hc1 j])
      _ = (m:ℝ) := by simp
  have hDT:0 ≤ D T := sum_nonneg (fun j _=>sq_nonneg _)
  linarith

/-- The paper's exact step size gives nm/sqrt(T), using |g_tj| ≤ n. -/
theorem normalized_regret {n m T : ℕ} (hn:1 ≤ n) (hT:1 ≤ T)
    (lam g : ℕ→Fin m→ℝ) (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+1/((n:ℝ)*Real.sqrt T)*g t j)))
    (hg:∀t<T,∀j,(g t j)^2 ≤ (n:ℝ)^2)
    (c : Fin m→ℝ) (hc0:∀j,0 ≤ c j) (hc1:∀j,c j ≤ 1) :
    (1/(T:ℝ))*(∑t∈range T,∑j,(c j-lam t j)*g t j)  ≤ 
      (n:ℝ)*m/Real.sqrt T := by
  have hnR:0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hTR:0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hsT:0<Real.sqrt T := Real.sqrt_pos.mpr hTR
  have hη:0<1/((n:ℝ)*Real.sqrt T) := by positivity
  have hh:=projected_regret lam g _ hη h0 hu c hc0 hc1
  have hgrad:(∑t∈range T,∑j,(g t j)^2)  ≤  (T:ℝ)*(m:ℝ)*(n:ℝ)^2 := by
    calc
      _  ≤  ∑t∈range T,∑j:Fin m,(n:ℝ)^2 := by
        apply sum_le_sum
        intro t ht
        exact sum_le_sum (fun j _=>hg t (mem_range.mp ht) j)
      _ = (T:ℝ)*(m:ℝ)*(n:ℝ)^2 := by simp [mul_assoc]
  have hηsq:0 ≤ (1/((n:ℝ)*Real.sqrt T))^2 := sq_nonneg _
  have hb:=hh.trans (add_le_add (le_refl (m:ℝ)) (mul_le_mul_of_nonneg_left hgrad hηsq))
  have hsq:(Real.sqrt (T:ℝ))^2=T := Real.sq_sqrt hTR.le
  have hscale:(1/((n:ℝ)*Real.sqrt T))^2*((T:ℝ)*m*(n:ℝ)^2)=(m:ℝ) := by
    field_simp
    nlinarith
  rw [hscale] at hb
  have hres:(∑t∈range T,∑j,(c j-lam t j)*g t j)  ≤  (n:ℝ)*Real.sqrt T*m := by
    have hs:(∑t∈range T,∑j,(c j-lam t j)*g t j) ≤
        ((m:ℝ)+m)/(2*(1/((n:ℝ)*Real.sqrt T))) :=
      (le_div_iff₀ (show 0<2*(1/((n:ℝ)*Real.sqrt T)) by positivity)).mpr (by
        simpa only [mul_comm] using hb)
    convert hs using 1 <;> field_simp <;> ring
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ hTR).mpr
  have he:(n:ℝ)*Real.sqrt T*m=(T:ℝ)*((n:ℝ)*m/Real.sqrt T) := by
    field_simp
    nlinarith
  rw [he] at hres
  simpa only [mul_comm] using hres

end ConsumerUtilityApprox.UnitDemand.OGDProof


set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset MeasureTheory ProbabilityTheory
open MultiItemRev.BundlingOpt
open scoped NNReal ENNReal

lemma alloc_mem_unit_interval {m : ℕ} (M : SBRand m) (v : Fin m→ℝ≥0) (j : Fin m) :
    0 ≤ M.alloc v j ∧ M.alloc v j ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have hh:(M v).toOuterMeasure {ω|ω.1=some j}  ≤  (1:ℝ≥0∞) := by
    rw [PMF.toOuterMeasure_apply]
    exact (ENNReal.tsum_le_tsum (fun ω=>Set.indicator_apply_le (fun _=>le_rfl))).trans_eq (M v).tsum_coe
  exact (ENNReal.toReal_mono (by norm_num) hh).trans_eq (by norm_num)

lemma qAlloc_mem_unit_interval {m : ℕ} (μ : Measure (Fin m→ℝ≥0)) [IsProbabilityMeasure μ]
    (M : SBRand m) (j : Fin m) : 0 ≤ qAlloc μ M.reduced j ∧ qAlloc μ M.reduced j ≤ 1 := by
  have h0:∀v,0 ≤ M.alloc v j := fun v=>(alloc_mem_unit_interval M v j).1
  have h1:∀v,M.alloc v j ≤ 1 := fun v=>(alloc_mem_unit_interval M v j).2
  refine ⟨integral_nonneg h0,?_⟩
  have hh:=integral_mono_of_nonneg (ae_of_all μ h0) (integrable_const (1:ℝ)) (ae_of_all μ h1)
  change (∫v,M.alloc v j ∂μ) ≤ 1
  convert hh using 1 <;> first | rfl | simp only [integral_const,probReal_univ,one_smul]

/-- Every actual public randomized single-buyer mechanism has the gradient
bound required by the normalized demand-weight regret estimate. -/
theorem actual_gradient_bound {n m : ℕ} (hn:1 ≤ n) (I : Instance n m)
    (M : ℕ→Fin n→SBRand m) (t : ℕ) (j : Fin m) :
    ((∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1)^2  ≤  (n:ℝ)^2 := by
  have h0:0 ≤ ∑i,qAlloc (I.buyerLaw i) (M t i).reduced j :=
    sum_nonneg (fun i _=>(qAlloc_mem_unit_interval _ _ j).1)
  have h1:(∑i,qAlloc (I.buyerLaw i) (M t i).reduced j) ≤ (n:ℝ) := by
    exact (sum_le_sum (fun i (_:i∈(univ:Finset (Fin n)))=>(qAlloc_mem_unit_interval _ _ j).2)).trans_eq (by simp)
  have hnR:(1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- Finite-sum identity and the hindsight 0/1 comparator turn projected
regret into the exact positive excess-request penalty. -/
theorem excess_requests_bound {n m T : ℕ} (hn:1 ≤ n) (hT:1 ≤ T)
    (lam r : ℕ→Fin m→ℝ) (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+1/((n:ℝ)*Real.sqrt T)*(r t j-1))))
    (hg:∀t<T,∀j,(r t j-1)^2 ≤ (n:ℝ)^2) :
    (∑j,max ((1/(T:ℝ))*(∑t∈range T,r t j)-1) 0)  ≤ 
      (1/(T:ℝ))*(∑t∈range T,∑j,lam t j*(r t j-1))+(n:ℝ)*m/Real.sqrt T := by
  classical
  let g:=fun t j=>r t j-1
  let avg:=fun j=>(1/(T:ℝ))*(∑t∈range T,r t j)-1
  let c:=fun j=>if 0<avg j then (1:ℝ) else 0
  have hc0:∀j,0 ≤ c j := by intro j;dsimp [c];split_ifs <;> norm_num
  have hc1:∀j,c j ≤ 1 := by intro j;dsimp [c];split_ifs <;> norm_num
  have hh:=normalized_regret hn hT lam g h0 hu hg c hc0 hc1
  have hTR:0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hgavg:∀j,(1/(T:ℝ))*(∑t∈range T,g t j)=avg j := by
    intro j
    simp only [g,avg,sum_sub_distrib,sum_const,card_range,nsmul_eq_mul,mul_one]
    field_simp
  have hcavg:∀j,c j*avg j=max (avg j) 0 := by
    intro j
    dsimp only [c]
    by_cases h:0<avg j
    · rw [if_pos h,one_mul,max_eq_left h.le]
    · rw [if_neg h,zero_mul,max_eq_right (by linarith)]
  have hsum:(1/(T:ℝ))*(∑t∈range T,∑j,(c j-lam t j)*g t j)=
      (∑j,max (avg j) 0)-(1/(T:ℝ))*(∑t∈range T,∑j,lam t j*g t j) := by
    simp only [sub_mul,sum_sub_distrib,mul_sub]
    congr 1
    rw [sum_comm,mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [← mul_sum]
    calc
      _ = c j*((1/(T:ℝ))*(∑t∈range T,g t j)) := by ring
      _ = _ := by rw [hgavg,hcavg]
  rw [hsum] at hh
  change (∑j,max (avg j) 0)  ≤  _
  dsimp only [g] at hh
  linarith

/-- Eq(C.8) instantiated on the actual mechanism allocation probabilities. -/
theorem actual_excess_requests_bound {n m T : ℕ} (hn:1 ≤ n) (hT:1 ≤ T) (I : Instance n m)
    (M : ℕ→Fin n→SBRand m) (lam : ℕ→Fin m→ℝ) (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+1/((n:ℝ)*Real.sqrt T)*
      ((∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1)))) :
    (∑j,max ((1/(T:ℝ))*(∑t∈range T,∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1) 0)  ≤ 
      (1/(T:ℝ))*(∑t∈range T,∑j,lam t j*((∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1))+
      (n:ℝ)*m/Real.sqrt T := by
  exact excess_requests_bound hn hT lam _ h0 hu (fun t ht j=>actual_gradient_bound hn I M t j)

end ConsumerUtilityApprox.UnitDemand.OGDProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma nonnegative_mean_summable {α : Type} (p : PMF α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ a ∈ p.support, 0 ≤ f a ∧ f a ≤ B) : Summable (fun a => (p a).toReal * f a) := by
  have hs := ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ennreal_mean_le p f B (fun a ha => (hf a ha).2)))
  apply hs.congr
  intro a
  rw [ENNReal.toReal_mul]
  by_cases ha : p a = 0
  · simp [ha]
  · rw [ENNReal.toReal_ofReal (hf a ((p.mem_support_iff a).mpr ha)).1]

noncomputable def mixture {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m) : SBRand m :=
  fun v => p.bind (fun a => M a v)

lemma allocation_as_mean {m : ℕ} (M : SBRand m) (w : Fin m → ℝ≥0) (j : Fin m) :
    M.alloc w j = ∑' ω, ((M w) ω).toReal * (if ω.1 = some j then (1 : ℝ) else 0) := by
  rw [mean_nonnegative (M w) _ (by intro ω hω; split_ifs <;> norm_num)]
  unfold SBRand.alloc
  congr 1
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro ω
  by_cases h : ω.1 = some j <;> simp [Set.indicator, h]

lemma mixture_allocation {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (w : Fin m → ℝ≥0) (j : Fin m) :
    (mixture p M).alloc w j = ∑' a, (p a).toReal * (M a).alloc w j := by
  rw [allocation_as_mean]
  change (∑' ω, ((p.bind (fun a => M a w)) ω).toReal *
    (if ω.1 = some j then (1 : ℝ) else 0)) = _
  rw [mean_bind p (fun a => M a w) _ 1 (by
    intro a ha ω hω
    split_ifs <;> norm_num)]
  simp_rw [← allocation_as_mean]

lemma supported_payment_bound {m : ℕ} (M : SBRand m) (hIR : M.IsExPostIR)
    (hN : M.HasNonnegPayments) (w : Fin m → ℝ≥0) (ω : SBOutcome m)
    (hω : ω ∈ (M w).support) : 0 ≤ ω.2 ∧ ω.2 ≤ ∑ j, (w j : ℝ) := by
  have hir := hIR w ω hω
  refine ⟨hN w ω hω, ?_⟩
  have hval : assignValue w ω.1 ≤ ∑ j, (w j : ℝ) := by
    cases hitem : ω.1 with
    | none => exact Finset.sum_nonneg (fun j _ => (w j).coe_nonneg)
    | some j => exact Finset.single_le_sum (fun k _ => (w k).coe_nonneg) (Finset.mem_univ j)
  linarith

lemma payment_bounds {m : ℕ} (M : SBRand m) (hIR : M.IsExPostIR)
    (hN : M.HasNonnegPayments) (w : Fin m → ℝ≥0) :
    0 ≤ M.pay w ∧ M.pay w ≤ ∑ j, (w j : ℝ) := by
  unfold SBRand.pay
  rw [mean_nonnegative (M w) Prod.snd
    (fun ω hω => (supported_payment_bound M hIR hN w ω hω).1)]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (ennreal_mean_le (M w) Prod.snd _
      (fun ω hω => (supported_payment_bound M hIR hN w ω hω).2))
  simpa only [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun j _ => (w j).coe_nonneg))] using hh

lemma mixture_payment {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hIR : ∀ a ∈ p.support, (M a).IsExPostIR)
    (hN : ∀ a ∈ p.support, (M a).HasNonnegPayments) (w : Fin m → ℝ≥0) :
    (mixture p M).pay w = ∑' a, (p a).toReal * (M a).pay w := by
  unfold SBRand.pay mixture
  exact mean_bind p (fun a => M a w) Prod.snd (∑ j, (w j : ℝ))
    (fun a ha ω hω => supported_payment_bound (M a) (hIR a ha) (hN a ha) w ω hω)

lemma mixture_IR_NPT {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hIR : ∀ a ∈ p.support, (M a).IsExPostIR)
    (hN : ∀ a ∈ p.support, (M a).HasNonnegPayments) :
    (mixture p M).IsExPostIR ∧ (mixture p M).HasNonnegPayments := by
  constructor
  · intro w ω hω
    obtain ⟨a, ha, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    exact hIR a ha w ω hω
  · intro w ω hω
    obtain ⟨a, ha, hω⟩ := (PMF.mem_support_bind_iff _ _ _).mp hω
    exact hN a ha w ω hω

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

noncomputable def reportUtility {m : ℕ} (M : SBRand m) (v w : Fin m → ℝ≥0) : ℝ :=
  ∑ j, M.alloc w j * (v j : ℝ) - M.pay w

lemma mixed_payoff_summable {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hIR : ∀ a ∈ p.support, (M a).IsExPostIR)
    (hN : ∀ a ∈ p.support, (M a).HasNonnegPayments) (v w : Fin m → ℝ≥0) :
    Summable (fun a => (p a).toReal * reportUtility (M a) v w) := by
  have ha (j : Fin m) : Summable (fun a => (p a).toReal * (M a).alloc w j * (v j : ℝ)) :=
    (nonnegative_mean_summable p (fun a => (M a).alloc w j) 1
      (fun a ha => OGDProof.alloc_mem_unit_interval _ _ _)).mul_right _
  have hp : Summable (fun a => (p a).toReal * (M a).pay w) :=
    nonnegative_mean_summable p (fun a => (M a).pay w) (∑ j, (w j : ℝ))
      (fun a ha => payment_bounds (M a) (hIR a ha) (hN a ha) w)
  have hs := (summable_sum (s := Finset.univ) (fun j _ => ha j)).sub hp
  apply hs.congr
  intro a
  simp only [reportUtility, mul_sub, Finset.mul_sum, mul_assoc]

lemma mixture_reportUtility {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hIR : ∀ a ∈ p.support, (M a).IsExPostIR)
    (hN : ∀ a ∈ p.support, (M a).HasNonnegPayments) (v w : Fin m → ℝ≥0) :
    reportUtility (mixture p M) v w = ∑' a, (p a).toReal * reportUtility (M a) v w := by
  have ha (j : Fin m) : Summable (fun a => (p a).toReal * (M a).alloc w j * (v j : ℝ)) :=
    (nonnegative_mean_summable p (fun a => (M a).alloc w j) 1
      (fun a ha => OGDProof.alloc_mem_unit_interval _ _ _)).mul_right _
  have hp : Summable (fun a => (p a).toReal * (M a).pay w) :=
    nonnegative_mean_summable p (fun a => (M a).pay w) (∑ j, (w j : ℝ))
      (fun a ha => payment_bounds (M a) (hIR a ha) (hN a ha) w)
  unfold reportUtility
  simp_rw [mixture_allocation, mixture_payment p M hIR hN]
  simp_rw [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun j _ => ha j), ← Summable.tsum_sub
    (summable_sum (s := Finset.univ) (fun j _ => ha j)) hp]
  apply tsum_congr
  intro a
  simp only [mul_sub, Finset.mul_sum, mul_assoc]

theorem mixture_IC {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hIC : ∀ a ∈ p.support, (M a).IsBIC)
    (hIR : ∀ a ∈ p.support, (M a).IsExPostIR)
    (hN : ∀ a ∈ p.support, (M a).HasNonnegPayments) : (mixture p M).IsBIC := by
  intro v w
  change reportUtility (mixture p M) v w ≤ reportUtility (mixture p M) v v
  rw [mixture_reportUtility p M hIR hN, mixture_reportUtility p M hIR hN]
  apply Summable.tsum_le_tsum _ (mixed_payoff_summable p M hIR hN v w)
    (mixed_payoff_summable p M hIR hN v v)
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (hIC a ((p.mem_support_iff a).mpr ha) v w) ENNReal.toReal_nonneg

end Utility7.ContentionProof


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset MeasureTheory ProbabilityTheory
open MultiItemRev.BundlingOpt
open scoped NNReal ENNReal

lemma clamp01_mem (x : ℝ) : 0  ≤  clamp01 x ∧ clamp01 x  ≤  1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩

lemma clamp01_eq (x : ℝ) (h0:0  ≤  x) (h1:x  ≤  1) : clamp01 x=x := by
  rw [clamp01,min_eq_left h1,max_eq_right h0]

lemma coin_true_toReal (x : ℝ) : (coin x true).toReal=clamp01 x := by
  simp only [coin,PMF.ofFintype_apply,if_true]
  rw [ENNReal.coe_toReal]
  change ((min (Real.toNNReal x) 1:ℝ≥0):ℝ)=max 0 (min x 1)
  rw [NNReal.coe_min,Real.coe_toNNReal',NNReal.coe_one]
  change min (max x 0) 1=max 0 (min x 1)
  by_cases h0:x ≤ 0
  · rw [max_eq_right h0,min_eq_left (by linarith : x ≤ 1)]
    simp [h0]
  · have hx:0 ≤ x := by linarith
    rw [max_eq_left hx]
    exact (max_eq_right (le_min hx (by norm_num))).symm

lemma pmf_real_sum {α : Type} [Fintype α] (p : PMF α) : ∑a,(p a).toReal=1 := by
  rw [← ENNReal.toReal_sum (fun a _=>p.apply_ne_top a)]
  have hs:(∑a,p a)=(1:ℝ≥0∞) := by simpa only [tsum_fintype] using p.tsum_coe
  rw [hs,ENNReal.toReal_one]

lemma choice_sum_le_one {m : ℕ} (p : PMF (Option (Fin m))) :
    (∑j,(p (some j)).toReal)  ≤  1 := by
  have hh:=pmf_real_sum p
  rw [Fintype.sum_option] at hh
  have hn:=ENNReal.toReal_nonneg (a:=p none)
  linarith

/-- Literal allocation formula for the public free lottery: candidate
selection is independent of the final success coin. -/
lemma freeLottery_alloc {m : ℕ} (ℓ : Fin m→ℝ) (v : Fin m→ℝ≥0) (j : Fin m) :
    (freeLotteryMech ℓ).alloc v j=
      ((uniformOn (lotCandidates v (fun j=>clamp01 (ℓ j)))) (some j)).toReal*clamp01 (ℓ j) := by
  classical
  unfold SBRand.alloc freeLotteryMech lotteryRequest
  rw [PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_bind_apply,tsum_fintype,Fintype.sum_option]
  simp only [PMF.toOuterMeasure_pure_apply,Set.mem_preimage,Set.mem_setOf_eq,Request.toOutcome,
    reduceCtorEq,if_false,mul_zero,zero_add]
  have he:∀i:Fin m,
      ((coin (clamp01 (ℓ i))).map (fun s=>if s then some (i,0) else none)).toOuterMeasure
        (Request.toOutcome ⁻¹' {ω:SBOutcome m|ω.1=some j})=
      if i=j then coin (clamp01 (ℓ i)) true else 0 := by
    intro i
    rw [PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_apply_fintype,Fintype.sum_bool]
    by_cases h:i=j <;> simp [Set.indicator_apply,Request.toOutcome,h]
  simp_rw [he]
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ j),ENNReal.toReal_mul,
    coin_true_toReal,clamp01_eq _ (clamp01_mem _).1 (clamp01_mem _).2]

lemma lotteryProb_mem {m : ℕ} (lam : Fin m→ℝ) (b : ℝ) (hb:0 ≤ b) (j : Fin m) :
    0 ≤ lotteryProb lam b j ∧ lotteryProb lam b j ≤ 1 := by
  unfold lotteryProb
  split_ifs with h
  · exact ⟨le_min (by norm_num) (div_nonneg hb h.le),min_le_left _ _⟩
  · norm_num

lemma lotteryProb_cost {m : ℕ} (lam : Fin m→ℝ) (hlam:∀j,0 ≤ lam j) (b : ℝ) (hb:0 ≤ b)
    (j : Fin m) : lam j*lotteryProb lam b j ≤ b := by
  unfold lotteryProb
  split_ifs with h
  · have hh:=mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (b/lam j)) (hlam j)
    rw [mul_div_cancel₀ _ (ne_of_gt h)] at hh
    exact hh
  · have hz:lam j=0 := by have hh:=hlam j;linarith
    rw [hz,zero_mul]
    exact hb

/-- The public free-lottery mechanism pays at most b in demand-weight cost
for every report, with its actual candidate and success-coin semantics. -/
theorem freeLottery_cost_pointwise {m : ℕ} (lam : Fin m→ℝ) (hlam:∀j,0 ≤ lam j)
    (b : ℝ) (hb:0 ≤ b) (v : Fin m→ℝ≥0) :
    (∑j,lam j*(freeLotteryMech (lotteryProb lam b)).alloc v j) ≤ b := by
  let p:=uniformOn (lotCandidates v (fun j=>clamp01 (lotteryProb lam b j)))
  have hh:∀j,lam j*(freeLotteryMech (lotteryProb lam b)).alloc v j ≤ (p (some j)).toReal*b := by
    intro j
    rw [freeLottery_alloc,clamp01_eq _ (lotteryProb_mem lam b hb j).1 (lotteryProb_mem lam b hb j).2]
    have hc:=mul_le_mul_of_nonneg_left (lotteryProb_cost lam hlam b hb j)
      (ENNReal.toReal_nonneg (a:=p (some j)))
    convert hc using 1 <;> first | rfl | ring
  calc
    _ ≤ ∑j,(p (some j)).toReal*b := Finset.sum_le_sum (fun j _=>hh j)
    _ = (∑j,(p (some j)).toReal)*b := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*b := mul_le_mul_of_nonneg_right (choice_sum_le_one p) hb
    _ = b := one_mul b

end ConsumerUtilityApprox.UnitDemand.OGDProof


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset MeasureTheory ProbabilityTheory
open MultiItemRev.BundlingOpt
open scoped NNReal ENNReal

lemma measurable_lotCandidates {m : ℕ} (ℓ : Fin m→ℝ) :
    Measurable (fun v:Fin m→ℝ≥0=>lotCandidates v ℓ) := by
  classical
  apply measurable_finset_iff.mpr
  intro j
  apply measurableSet_setOfPred.mp
  simp only [lotCandidates,Finset.mem_filter,Finset.mem_univ,true_and]
  have hm:∀j,Measurable (fun v:Fin m→ℝ≥0=>ℓ j*(v j:ℝ)) := by intro j;fun_prop
  have ha:MeasurableSet {v:Fin m→ℝ≥0|∀k,ℓ k*(v k:ℝ) ≤ ℓ j*(v j:ℝ)} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k=>measurableSet_le (hm k) (hm j))
  exact (measurableSet_lt measurable_const (hm j)).inter ha

lemma measurable_freeLottery_alloc {m : ℕ} (ℓ : Fin m→ℝ) (j : Fin m) :
    Measurable (fun v:Fin m→ℝ≥0=>(freeLotteryMech ℓ).alloc v j) := by
  have hpoint:Measurable (fun S:Finset (Fin m)=>(uniformOn S (some j)).toReal) :=
    measurable_of_countable _
  have hh:=hpoint.comp (measurable_lotCandidates (fun j=>clamp01 (ℓ j)))
  have he:(fun v:Fin m→ℝ≥0=>(freeLotteryMech ℓ).alloc v j)=
      (fun v=>(uniformOn (lotCandidates v (fun j=>clamp01 (ℓ j))) (some j)).toReal*clamp01 (ℓ j)) :=
    funext (fun v=>freeLottery_alloc ℓ v j)
  rw [he]
  exact hh.mul_const _

lemma freeLottery_payment_support_zero {m : ℕ} (ℓ : Fin m→ℝ) (v : Fin m→ℝ≥0)
    (ω : SBOutcome m) (hω:ω∈(freeLotteryMech ℓ v).support) : ω.2=0 := by
  unfold freeLotteryMech at hω
  obtain ⟨req,hreq,rfl⟩:=(PMF.mem_support_map_iff _ _ _).mp hω
  unfold lotteryRequest at hreq
  obtain ⟨c,hc,hreq⟩:=PMF.mem_support_bind_iff _ _ _ |>.mp hreq
  cases c with
  | none =>
    have hr:req=none := (PMF.mem_support_pure_iff _ _).mp hreq
    rw [hr]
    rfl
  | some j =>
    obtain ⟨b,hb,rfl⟩:=(PMF.mem_support_map_iff _ _ _).mp hreq
    cases b <;> rfl

lemma freeLottery_pay_zero {m : ℕ} (ℓ : Fin m→ℝ) (v : Fin m→ℝ≥0) :
    (freeLotteryMech ℓ).pay v=0 := by
  unfold SBRand.pay
  have he:∀ω:SBOutcome m,((freeLotteryMech ℓ v) ω).toReal*ω.2=0 := by
    intro ω
    by_cases hω:ω∈(freeLotteryMech ℓ v).support
    · rw [freeLottery_payment_support_zero ℓ v ω hω,mul_zero]
    · have hz:(freeLotteryMech ℓ v) ω=0 := ((freeLotteryMech ℓ v).apply_eq_zero_iff _).mpr hω
      rw [hz,ENNReal.toReal_zero,zero_mul]
  simp only [he,tsum_zero]

end ConsumerUtilityApprox.UnitDemand.OGDProof


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset MeasureTheory ProbabilityTheory
open MultiItemRev.BundlingOpt
open scoped NNReal ENNReal

lemma freeLottery_alloc_integrable {m : ℕ} (μ : Measure (Fin m→ℝ≥0)) [IsProbabilityMeasure μ]
    (ℓ : Fin m→ℝ) (j : Fin m) : Integrable (fun v=>(freeLotteryMech ℓ).alloc v j) μ := by
  refine ⟨(measurable_freeLottery_alloc ℓ j).aestronglyMeasurable,?_⟩
  apply HasFiniteIntegral.of_bounded (C:=1)
  apply ae_of_all
  intro v
  rw [Real.norm_eq_abs,abs_of_nonneg (alloc_mem_unit_interval _ v j).1]
  exact (alloc_mem_unit_interval _ v j).2

/-- The pointwise cost budget is preserved by the exact public qAlloc
integral. Measurability is proved for the actual candidate rule. -/
theorem freeLottery_cost_bound {m : ℕ} (μ : Measure (Fin m→ℝ≥0)) [IsProbabilityMeasure μ]
    (lam : Fin m→ℝ) (hlam:∀j,0 ≤ lam j) (b : ℝ) (hb:0 ≤ b) :
    (∑j,lam j*qAlloc μ (freeLotteryMech (lotteryProb lam b)).reduced j) ≤ b := by
  have hint:∀j,Integrable (fun v=>lam j*(freeLotteryMech (lotteryProb lam b)).alloc v j) μ :=
    fun j=>(freeLottery_alloc_integrable μ _ j).const_mul _
  have h0:∀v,0 ≤ ∑j,lam j*(freeLotteryMech (lotteryProb lam b)).alloc v j :=
    fun v=>sum_nonneg (fun j _=>mul_nonneg (hlam j) (alloc_mem_unit_interval _ v j).1)
  calc
    _ = ∫v,∑j,lam j*(freeLotteryMech (lotteryProb lam b)).alloc v j ∂μ := by
      rw [integral_finset_sum _ (fun j _=>hint j)]
      apply sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      rfl
    _ ≤ ∫v,b ∂μ := integral_mono_of_nonneg (ae_of_all μ h0) (integrable_const b)
      (ae_of_all μ (freeLottery_cost_pointwise lam hlam b hb))
    _ = b := by simp

/-- Approximate free-lottery search loses at most gamma in its Lagrangian
half-utility guarantee, including the mechanism's actual allocation cost. -/
theorem freeLottery_lagrangian_ge_half {m : ℕ} (μ : Measure (Fin m→ℝ≥0)) [IsProbabilityMeasure μ]
    (lam : Fin m→ℝ) (hlam:∀j,0 ≤ lam j) (b γ : ℝ) (hb:0 ≤ b)
    (hU:2*b-2*γ ≤ utility μ (freeLotteryMech (lotteryProb lam b)).reduced) :
    utility μ (freeLotteryMech (lotteryProb lam b)).reduced-
      (∑j,lam j*qAlloc μ (freeLotteryMech (lotteryProb lam b)).reduced j) ≥
      utility μ (freeLotteryMech (lotteryProb lam b)).reduced/2-γ := by
  have hc:=freeLottery_cost_bound μ lam hlam b hb
  linarith

end ConsumerUtilityApprox.UnitDemand.OGDProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma uniformOn_some_probability {m : ℕ} (S : Finset (Fin m)) (j : Fin m) :
    ((ConsumerUtilityApprox.UnitDemand.uniformOn S) (some j)).toReal =
      if j ∈ S then 1 / (S.card : ℝ) else 0 := by
  unfold ConsumerUtilityApprox.UnitDemand.uniformOn
  by_cases hS : S.Nonempty
  · rw [dif_pos hS]
    simp only [PMF.map_apply, Option.some.injEq, tsum_ite_eq', PMF.uniformOfFinset_apply]
    split_ifs <;> simp
  · rw [dif_neg hS]
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [he]

lemma random_choice_le_maximum {m : ℕ} [Nonempty (Fin m)] (p : PMF (Option (Fin m)))
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) :
    (∑ j, (p (some j)).toReal * a j) ≤ SurplusProof.maximum (fun j (_ : Unit) => a j) () := by
  let M := SurplusProof.maximum (fun j (_ : Unit) => a j) ()
  have hM : 0 ≤ M := SurplusProof.maximum_nonneg _ (fun j _ => ha j) ()
  calc
    _ ≤ ∑ j, (p (some j)).toReal * M := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact Finset.le_sup' (fun j => a j) (Finset.mem_univ j)
    _ = (∑ j, (p (some j)).toReal) * M := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right (OGDProof.choice_sum_le_one p) hM
    _ = _ := one_mul _

lemma lottery_truthful_value {m : ℕ} [Nonempty (Fin m)] (lot : Fin m → ℝ)
    (v : Fin m → ℝ≥0) :
    (∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn
      (lotCandidates v (fun j => clamp01 (lot j)))) (some j)).toReal *
        (clamp01 (lot j) * (v j : ℝ))) =
      SurplusProof.maximum (fun j (_ : Unit) => clamp01 (lot j) * (v j : ℝ)) () := by
  let a : Fin m → ℝ := fun j => clamp01 (lot j) * (v j : ℝ)
  have ha (j : Fin m) : 0 ≤ a j := mul_nonneg (OGDProof.clamp01_mem _).1 (v j).coe_nonneg
  let v' : Fin m → ℝ≥0 := fun j => ⟨a j, ha j⟩
  have hsur (j : Fin m) : surplus (v' j) 0 = a j := by
    simp only [surplus, ENNReal.zero_ne_top, if_false, ENNReal.toReal_zero, sub_zero]
    change max (a j) 0 = a j
    exact max_eq_left (ha j)
  have hcand : lotCandidates v (fun j => clamp01 (lot j)) = udCandidates v' (fun _ => 0) := by
    ext j
    simp only [lotCandidates, udCandidates, Finset.mem_filter, Finset.mem_univ, true_and, hsur]
    rfl
  have hh := SurplusProof.choice_utility_maximum v' (fun _ => 0)
  simp only [udChoice, hsur] at hh
  simpa only [uniformOn_some_probability, hcand, a] using hh

theorem freeLottery_IC {m : ℕ} (lot : Fin m → ℝ) : (freeLotteryMech lot).IsBIC := by
  cases m with
  | zero =>
    intro v w
    simp [buyerPayoff, SBRand.reduced, OGDProof.freeLottery_pay_zero]
  | succ m =>
    intro v w
    have hh := random_choice_le_maximum
      (ConsumerUtilityApprox.UnitDemand.uniformOn (lotCandidates w (fun j => clamp01 (lot j))))
      (fun j => clamp01 (lot j) * (v j : ℝ))
      (fun j => mul_nonneg (OGDProof.clamp01_mem _).1 (v j).coe_nonneg)
    have he := lottery_truthful_value lot v
    change (∑ j, (freeLotteryMech lot).alloc w j * (v j : ℝ)) - (freeLotteryMech lot).pay w ≤ _
    unfold buyerPayoff
    simp only [SBRand.reduced, OGDProof.freeLottery_pay_zero, sub_zero, OGDProof.freeLottery_alloc]
    calc
      _ = ∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn
          (lotCandidates w (fun j => clamp01 (lot j)))) (some j)).toReal *
            (clamp01 (lot j) * (v j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := hh
      _ = _ := by
        rw [← he]
        apply Finset.sum_congr rfl
        intro j _
        ring

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

def fixedPriceOutcome {m : ℕ} (t : Fin m → ℝ≥0∞) : Option (Fin m) → SBOutcome m
  | none => (none, 0)
  | some j => (some j, (t j).toReal)

noncomputable def fixedPriceMech {m : ℕ} (t : Fin m → ℝ≥0∞) : SBRand m :=
  fun w => (ConsumerUtilityApprox.UnitDemand.uniformOn (udCandidates w t)).map (fixedPriceOutcome t)

lemma fixedPrice_allocation {m : ℕ} (t : Fin m → ℝ≥0∞) (w : Fin m → ℝ≥0) (j : Fin m) :
    (fixedPriceMech t).alloc w j =
      ((ConsumerUtilityApprox.UnitDemand.uniformOn (udCandidates w t)) (some j)).toReal := by
  unfold SBRand.alloc fixedPriceMech
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_fintype, Fintype.sum_option]
  simp only [Set.indicator, Set.mem_preimage, Set.mem_setOf_eq, fixedPriceOutcome,
    reduceCtorEq, if_false, zero_add, Option.some.injEq]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma fixedPrice_payment {m : ℕ} (t : Fin m → ℝ≥0∞) (w : Fin m → ℝ≥0) :
    (fixedPriceMech t).pay w = ∑ j,
      ((ConsumerUtilityApprox.UnitDemand.uniformOn (udCandidates w t)) (some j)).toReal * (t j).toReal := by
  unfold SBRand.pay fixedPriceMech
  rw [mean_map _ (fixedPriceOutcome t) Prod.snd (by
    intro c hc
    cases c <;> simp [fixedPriceOutcome, ENNReal.toReal_nonneg])]
  rw [tsum_fintype, Fintype.sum_option]
  simp only [fixedPriceOutcome, mul_zero, zero_add]

lemma fixedPrice_payoff {m : ℕ} (t : Fin m → ℝ≥0∞) (v w : Fin m → ℝ≥0) :
    (∑ j, (fixedPriceMech t).reduced.q w j * (v j : ℝ)) - (fixedPriceMech t).reduced.s w =
      ∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn (udCandidates w t)) (some j)).toReal *
        ((v j : ℝ) - (t j).toReal) := by
  simp only [SBRand.reduced, fixedPrice_allocation, fixedPrice_payment, mul_sub,
    Finset.sum_sub_distrib]

lemma truthful_price_surplus {m : ℕ} (t : Fin m → ℝ≥0∞) (v : Fin m → ℝ≥0)
    (j : Fin m) (hj : j ∈ udCandidates v t) :
    (v j : ℝ) - (t j).toReal = surplus (v j) (t j) := by
  have hpos := (SurplusProof.choice_mem v t j hj).1
  have ht : t j ≠ ⊤ := ne_top_of_lt ((SurplusProof.surplus_pos_iff _ _).mp hpos)
  unfold surplus at hpos ⊢
  rw [if_neg ht] at hpos ⊢
  exact (max_eq_left (by rcases lt_max_iff.mp hpos with h | h <;> linarith)).symm

lemma fixedPrice_truthful_utility {m : ℕ} [Nonempty (Fin m)] (t : Fin m → ℝ≥0∞)
    (v : Fin m → ℝ≥0) : buyerPayoff (fixedPriceMech t).reduced v =
      SurplusProof.maximum (fun j (_ : Unit) => surplus (v j) (t j)) () := by
  unfold buyerPayoff
  rw [fixedPrice_payoff]
  calc
    _ = ∑ j, udChoice v t j * surplus (v j) (t j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [uniformOn_some_probability]
      by_cases hj : j ∈ udCandidates v t
      · simp only [if_pos hj, udChoice, truthful_price_surplus t v j hj]
      · simp [udChoice, hj]
    _ = _ := SurplusProof.choice_utility_maximum v t

theorem fixedPrice_IC {m : ℕ} (t : Fin m → ℝ≥0∞) : (fixedPriceMech t).IsBIC := by
  cases m with
  | zero => intro v w; simp [buyerPayoff, SBRand.reduced, fixedPrice_payment]
  | succ m =>
    intro v w
    rw [fixedPrice_payoff, fixedPrice_truthful_utility]
    calc
      _ ≤ ∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn (udCandidates w t)) (some j)).toReal *
          surplus (v j) (t j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [uniformOn_some_probability]
        by_cases hj : j ∈ udCandidates w t
        · rw [if_pos hj]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have ht : t j ≠ ⊤ := ne_top_of_lt
            ((SurplusProof.surplus_pos_iff _ _).mp (SurplusProof.choice_mem w t j hj).1)
          simp only [surplus, if_neg ht]
          exact le_max_left _ _
        · simp [hj]
      _ ≤ _ := random_choice_le_maximum _ (fun j => surplus (v j) (t j))
        (fun j => SurplusProof.surplus_nonneg _ _)

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma request_safety {m : ℕ} (F : (Fin m → ℝ≥0) → PMF (Request m))
    (hF : ∀ w j p, some (j, p) ∈ (F w).support → 0 ≤ p ∧ p ≤ w j) :
    SBRand.IsExPostIR (fun w => (F w).map Request.toOutcome) ∧
      SBRand.HasNonnegPayments (fun w => (F w).map Request.toOutcome) := by
  have hp (w : Fin m → ℝ≥0) (ω : SBOutcome m)
      (hω : ω ∈ ((F w).map Request.toOutcome).support) :
      0 ≤ assignValue w ω.1 - ω.2 ∧ 0 ≤ ω.2 := by
    obtain ⟨req, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    cases req with
    | none => simp [Request.toOutcome, assignValue]
    | some a =>
      obtain ⟨j, p⟩ := a
      have hh := hF w j p hr
      exact ⟨sub_nonneg.mpr hh.2, hh.1⟩
  exact ⟨fun w ω hω => (hp w ω hω).1, fun w ω hω => (hp w ω hω).2⟩

lemma freeLottery_safety {m : ℕ} (lot : Fin m → ℝ) :
    (freeLotteryMech lot).IsExPostIR ∧ (freeLotteryMech lot).HasNonnegPayments :=
  request_safety (lotteryRequest lot) (fun w j p hp => lottery_request_valid lot w j p hp)

lemma postedPrice_safety {m : ℕ} (pr : Fin m → TwoPointPrice) :
    (postedPriceMech pr).IsExPostIR ∧ (postedPriceMech pr).HasNonnegPayments :=
  request_safety (pricingRequest pr) (fun w j p hp => pricing_request_valid pr w j p hp)

lemma fixedPrice_safety {m : ℕ} (t : Fin m → ℝ≥0∞) :
    (fixedPriceMech t).IsExPostIR ∧ (fixedPriceMech t).HasNonnegPayments := by
  have hp (w : Fin m → ℝ≥0) (ω : SBOutcome m) (hω : ω ∈ (fixedPriceMech t w).support) :
      0 ≤ assignValue w ω.1 - ω.2 ∧ 0 ≤ ω.2 := by
    obtain ⟨c, hc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    cases c with
    | none => simp [fixedPriceOutcome, assignValue]
    | some j =>
      have hj := uniformOn_support _ j hc
      have hs := (SurplusProof.choice_mem w t j hj).1
      change 0 ≤ (w j : ℝ) - (t j).toReal ∧ 0 ≤ (t j).toReal
      exact ⟨(truthful_price_surplus t w j hj).symm ▸ hs.le, ENNReal.toReal_nonneg⟩
  exact ⟨fun w ω hω => (hp w ω hω).1, fun w ω hω => (hp w ω hω).2⟩

noncomputable def nullMech {m : ℕ} : SBRand m := fun _ => PMF.pure (none, 0)

lemma nullMech_IC {m : ℕ} : (nullMech : SBRand m).IsBIC := by
  intro v w
  simp [nullMech, SBRand.reduced, SBRand.alloc, SBRand.pay, buyerPayoff,
    PMF.toOuterMeasure_pure_apply]

lemma nullMech_safety {m : ℕ} : (nullMech : SBRand m).IsExPostIR ∧
    (nullMech : SBRand m).HasNonnegPayments := by
  constructor <;> intro w ω hω
  all_goals
    have he : ω = (none, 0) := (PMF.mem_support_pure_iff _ _).mp hω
    subst ω
    simp [assignValue]

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma map_cons_apply {α : Type} {n : ℕ} (p : PMF (Fin n → α)) (a b : α) (v : Fin n → α) :
    (p.map (fun g : Fin n → α => (Fin.cons a g : Fin (n + 1) → α)))
      (Fin.cons b v) = if b = a then p v else 0 := by
  classical
  simp only [PMF.map_apply, Fin.cons_inj]
  by_cases h : b = a
  · simp [h]
  · simp [h]

lemma map_cons_apply_general {α : Type} {n : ℕ} (p : PMF (Fin n → α)) (a : α)
    (v : Fin (n + 1) → α) :
    (p.map (fun g : Fin n → α => (Fin.cons a g : Fin (n + 1) → α))) v =
      if v 0 = a then p (Fin.tail v) else 0 := by
  classical
  simpa only [Fin.cons_self_tail] using map_cons_apply p a (v 0) (Fin.tail v)

lemma indep_apply {α : Type} (n : ℕ) (p : Fin n → PMF α) (v : Fin n → α) :
    indep n p v = ∏ i, p i (v i) := by
  classical
  induction n with
  | zero => simp [indep, PMF.pure_apply]; exact Subsingleton.elim _ _
  | succ n ih =>
    rw [indep, PMF.bind_apply]
    simp_rw [map_cons_apply_general, mul_ite, mul_zero]
    simp only [tsum_ite_eq, tsum_ite_eq']
    rw [ih]
    rw [Fin.prod_univ_succ]
    rfl

lemma indep_eval {α : Type} (n : ℕ) (p : Fin n → PMF α) (i : Fin n) :
    (indep n p).map (fun v => v i) = p i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      calc
        _ = (p 0).bind (fun a => (indep n (fun i => p i.succ)).map (fun _ => a)) := by
          simp only [indep, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_zero]
        _ = (p 0).bind PMF.pure := by
          congr 1
          funext a
          exact PMF.map_const _ _
        _ = _ := PMF.bind_pure _
    | succ i =>
      simpa only [indep, PMF.map_bind, PMF.map_comp, Function.comp_def, Fin.cons_succ,
        ih, PMF.bind_const]

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

noncomputable def requestMech {n m : ℕ} (D : MechDescription n m) (i : Fin n) : SBRand m :=
  fun v => (D.request i v).map Request.toOutcome

lemma preLaw_marginal {n m : ℕ} (D : MechDescription n m) (v : Profile n m) (i : Fin n) :
    (D.preLaw v).map (fun ω => (ω.1 i, ω.2 i)) = requestMech D i (v i) := by
  unfold MechDescription.preLaw requestMech
  rw [PMF.map_comp]
  have hf : (fun req : Fin n → Request m =>
      (((fun k => (req k).map Prod.fst) i),
        ((fun k => match req k with | some (_, p) => p | none => 0) i))) =
      (Request.toOutcome ∘ (fun req : Fin n → Request m => req i)) := by
    funext req
    cases h : req i with
    | none => simp [h, Request.toOutcome]
    | some a => obtain ⟨j, p⟩ := a; simp [h, Request.toOutcome]
  change ((indep n (fun k => D.request k (v k))).map
    (fun req : Fin n → Request m =>
      (((fun k => (req k).map Prod.fst) i),
        ((fun k => match req k with | some (_, p) => p | none => 0) i)))) = _
  rw [hf, ← PMF.map_comp, indep_eval]

lemma preLaw_allocation {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) (j : Fin m) : D.preLaw.reduced.x v i j = (requestMech D i).alloc (v i) j := by
  have h := congrArg (fun p : PMF (SBOutcome m) => p.toOuterMeasure {ω | ω.1 = some j})
    (preLaw_marginal D v i)
  rw [PMF.toOuterMeasure_map_apply] at h
  exact congrArg ENNReal.toReal h

lemma preLaw_interimAllocation {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (i : Fin n) (w : Fin m → ℝ≥0) (j : Fin m) :
    D.preLaw.reduced.interimAlloc I i w j = (requestMech D i).alloc w j := by
  unfold RMech.interimAlloc
  simp only [preLaw_allocation, Function.update_self, integral_const, probReal_univ, one_smul]

lemma preLaw_nonnegative {n m : ℕ} (D : MechDescription n m) : D.preLaw.HasNonnegPayments := by
  intro v ω hω i
  unfold MechDescription.preLaw at hω
  obtain ⟨req, hr, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
  have hri := indep_support_coordinate _ _ hr i
  cases hreq : req i with
  | none => simp [hreq]
  | some a =>
    obtain ⟨j, p⟩ := a
    rw [hreq] at hri
    change 0 ≤ (match req i with | some (_, p) => p | none => 0)
    rw [hreq]
    exact (request_valid D i (v i) j p hri).1

lemma preLaw_payment {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) : D.preLaw.reduced.p v i = (requestMech D i).pay (v i) := by
  have hh := mean_map (D.preLaw v) (fun ω => (ω.1 i, ω.2 i)) (fun ω => ω.2)
    (fun ω hω => preLaw_nonnegative D v ω hω i)
  rw [preLaw_marginal] at hh
  exact hh.symm

lemma preLaw_interimPayment {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (i : Fin n) (w : Fin m → ℝ≥0) :
    D.preLaw.reduced.interimPay I i w = (requestMech D i).pay w := by
  unfold RMech.interimPay
  simp only [preLaw_payment, Function.update_self, integral_const, probReal_univ, one_smul]

lemma preLaw_BIC_of_requestIC {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hIC : ∀ i, (requestMech D i).IsBIC) : D.preLaw.IsBIC I := by
  intro i v w
  unfold RMech.interimUtil
  simp only [preLaw_interimAllocation, preLaw_interimPayment]
  simpa only [MultiItemRev.BundlingOpt.buyerPayoff, SBRand.reduced, mul_comm] using hIC i v w

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

def Good {m : ℕ} (M : SBRand m) : Prop := M.IsBIC ∧ M.IsExPostIR ∧ M.HasNonnegPayments

lemma mixture_good {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (hM : ∀ a, Good (M a)) : Good (mixture p M) := by
  have hs := mixture_IR_NPT p M (fun a _ => (hM a).2.1) (fun a _ => (hM a).2.2)
  exact ⟨mixture_IC p M (fun a _ => (hM a).1) (fun a _ => (hM a).2.1)
    (fun a _ => (hM a).2.2), hs⟩

lemma postedPrice_as_mixture {m : ℕ} (pr : Fin m → TwoPointPrice) :
    postedPriceMech pr = mixture (indep m (fun j => (pr j).law)) fixedPriceMech := by
  funext v
  unfold postedPriceMech pricingRequest mixture
  rw [PMF.map_bind]
  congr 1
  funext t
  unfold fixedPriceMech
  rw [PMF.map_comp]
  congr 1
  funext c
  cases c <;> rfl

lemma postedPrice_good {m : ℕ} (pr : Fin m → TwoPointPrice) : Good (postedPriceMech pr) := by
  rw [postedPrice_as_mixture]
  apply mixture_good
  intro t
  exact ⟨fixedPrice_IC t, fixedPrice_safety t⟩

lemma freeLottery_good {m : ℕ} (lot : Fin m → ℝ) : Good (freeLotteryMech lot) :=
  ⟨freeLottery_IC lot, freeLottery_safety lot⟩

lemma null_good {m : ℕ} : Good (nullMech : SBRand m) := ⟨nullMech_IC, nullMech_safety⟩

noncomputable def roundMech {n m : ℕ} (D : MechDescription n m) (i : Fin n) (t : ℕ) : SBRand m :=
  mixture (coin (D.w i t)) (fun b =>
    if b then postedPriceMech (D.price i t) else freeLotteryMech (D.lottery i t))

lemma round_good {n m : ℕ} (D : MechDescription n m) (i : Fin n) (t : ℕ) : Good (roundMech D i t) := by
  apply mixture_good
  intro b
  cases b
  · exact freeLottery_good _
  · exact postedPrice_good _

noncomputable def participateMech {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (h : (Finset.range D.T).Nonempty) : SBRand m :=
  mixture (PMF.uniformOfFinset (Finset.range D.T) h) (roundMech D i)

lemma participate_good {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (h : (Finset.range D.T).Nonempty) : Good (participateMech D i h) :=
  mixture_good _ _ (round_good D i)

lemma request_as_mixtures {n m : ℕ} (D : MechDescription n m) (i : Fin n) :
    requestMech D i =
      if h : (Finset.range D.T).Nonempty then
        mixture (coin D.ρ) (fun part => if part then participateMech D i h else nullMech)
      else nullMech := by
  classical
  funext v
  unfold requestMech MechDescription.request
  by_cases hT : (Finset.range D.T).Nonempty
  · rw [dif_pos hT, dif_pos hT]
    unfold mixture
    rw [PMF.map_bind]
    congr 1
    funext part
    cases part with
    | false => simp [PMF.pure_map, Request.toOutcome, nullMech]
    | true =>
      simp only [↓reduceIte]
      unfold participateMech mixture
      rw [PMF.map_bind]
      congr 1
      funext t
      unfold roundMech mixture
      rw [PMF.map_bind]
      congr 1
      funext br
      cases br <;> rfl
  · rw [dif_neg hT, dif_neg hT]
    simp [PMF.pure_map, Request.toOutcome, nullMech]

theorem request_good {n m : ℕ} (D : MechDescription n m) (i : Fin n) : Good (requestMech D i) := by
  rw [request_as_mixtures]
  split_ifs with hT
  · apply mixture_good
    intro part
    cases part
    · exact null_good
    · exact participate_good D i hT
  · exact null_good

theorem preLaw_BIC {n m : ℕ} (I : Instance n m) (D : MechDescription n m) : D.preLaw.IsBIC I :=
  preLaw_BIC_of_requestIC I D (fun i => (request_good D i).1)

end Utility7.ContentionProof


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


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma payoff_bounds {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (v : Fin m → ℝ≥0) : 0 ≤ buyerPayoff M v ∧ buyerPayoff M v ≤ ∑ j, (v j : ℝ) := by
  refine ⟨hM.2.2.1 v, ?_⟩
  have hs : (∑ j, M.q v j * (v j : ℝ)) ≤ ∑ j, (v j : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_of_le_one_left (v j).coe_nonneg (hM.1 v j).2
  unfold buyerPayoff
  linarith [hM.2.2.2.1 v]

lemma measurable_payoff {m : ℕ} (M : Mechanism (Fin m)) (hM : IsMeasurableMech M) :
    Measurable (buyerPayoff M) := by
  unfold buyerPayoff
  apply Measurable.sub _ hM.2
  exact Finset.measurable_sum Finset.univ (fun j _ => (hM.1 j).mul (by fun_prop))

lemma integrable_value {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (j : Fin m) :
    Integrable (fun v : Fin m → ℝ≥0 => (v j : ℝ)) (vecLaw G) := by
  exact integrable_comp_eval (μ := fun k => (G k : Measure ℝ≥0)) (i := j) (hG j).1

lemma integrable_allocation {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) :
    Integrable (fun v => M.q v j) (vecLaw G) := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (hM.2.2.2.2.1 j).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (hM.1 v j).1]
  exact (hM.1 v j).2

lemma integrable_payoff {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) :
    Integrable (buyerPayoff M) (vecLaw G) := by
  apply Integrable.mono' (integrable_finsetSum Finset.univ (fun j _ => integrable_value G hG j))
    (measurable_payoff M hM.2.2.2.2).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (payoff_bounds M hM v).1]
  exact (payoff_bounds M hM v).2

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma payoff_mono {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (v w : Fin m → ℝ≥0) (hvw : ∀ j, v j ≤ w j) : buyerPayoff M v ≤ buyerPayoff M w := by
  have hic := hM.2.1 w v
  have hs : (∑ j, M.q v j * (v j : ℝ)) ≤ ∑ j, M.q v j * (w j : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hvw j) (hM.1 v j).1
  unfold buyerPayoff
  exact (sub_le_sub_right hs _).trans hic

lemma deleted_payoff_le {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (v : Fin m → ℝ≥0) (j : Fin m) :
    buyerPayoff M (Function.update v j 0) ≤ buyerPayoff M v := by
  classical
  apply payoff_mono M hM
  intro k
  by_cases hk : k = j
  · subst k; simp
  · simp [Function.update_of_ne hk]

def deletionComponent {m : ℕ} (M : Mechanism (Fin m)) (j : Fin m) (v : Fin m → ℝ≥0) : ℝ :=
  buyerPayoff M v - buyerPayoff M (Function.update v j 0)

lemma deletionComponent_nonneg {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) (v : Fin m → ℝ≥0) : 0 ≤ deletionComponent M j v :=
  sub_nonneg.mpr (deleted_payoff_le M hM v j)

lemma integrable_deleted_payoff {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Integrable (fun v => buyerPayoff M (Function.update v j 0)) (vecLaw G) := by
  apply Integrable.mono' (integrable_payoff G hG M hM)
    ((measurable_payoff M hM.2.2.2.2).comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with v
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (payoff_bounds M hM _).1]
  exact deleted_payoff_le M hM v j

lemma integrable_deletionComponent {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Integrable (deletionComponent M j) (vecLaw G) :=
  (integrable_payoff G hG M hM).sub (integrable_deleted_payoff G hG M hM j)

lemma abs_payoff_sub_le_deletions {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) (v w : Fin m → ℝ≥0) (he : Function.update v j 0 = Function.update w j 0) :
    |buyerPayoff M v - buyerPayoff M w| ≤ deletionComponent M j v + deletionComponent M j w := by
  have hv := deletionComponent_nonneg M hM j v
  have hw := deletionComponent_nonneg M hM j w
  unfold deletionComponent at hv hw ⊢
  rw [he] at hv ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.BenchmarkProof

noncomputable def hybrid {m : ℕ} (s : Finset (Fin m))
    (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) (j : Fin m) : ℝ≥0 :=
  if j ∈ s then vw.1 j else vw.2 j

lemma measurePreserving_hybrid {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (s : Finset (Fin m)) :
    MeasurePreserving (hybrid s) ((vecLaw G).prod (vecLaw G)) (vecLaw G) := by
  classical
  let ν := fun j => (G j : Measure ℝ≥0)
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ≥0 ℝ≥0 (Fin m)
  have he : MeasurePreserving e (Measure.pi (fun j => (ν j).prod (ν j)))
      ((Measure.pi ν).prod (Measure.pi ν)) :=
    measurePreserving_arrowProdEquivProdArrow ℝ≥0 ℝ≥0 (Fin m) ν ν
  have hp : MeasurePreserving (fun z : Fin m → ℝ≥0 × ℝ≥0 =>
      fun j => if j ∈ s then (z j).1 else (z j).2)
      (Measure.pi (fun j => (ν j).prod (ν j))) (Measure.pi ν) := by
    apply measurePreserving_pi (fun j => (ν j).prod (ν j)) ν
      (f := fun j z => if j ∈ s then z.1 else z.2)
    intro j
    by_cases hj : j ∈ s
    · simpa only [if_pos hj] using (measurePreserving_fst (μ := ν j) (ν := ν j))
    · simpa only [if_neg hj] using (measurePreserving_snd (μ := ν j) (ν := ν j))
  exact hp.comp (MeasurePreserving.symm e he)

lemma hybrid_univ {m : ℕ} (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) :
    hybrid Finset.univ vw = vw.1 := by funext j; simp [hybrid]

lemma hybrid_empty {m : ℕ} (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) :
    hybrid ∅ vw = vw.2 := by funext j; simp [hybrid]

lemma integral_hybrid {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (s : Finset (Fin m)) (f : (Fin m → ℝ≥0) → ℝ) (hf : AEStronglyMeasurable f (vecLaw G)) :
    (∫ vw, f (hybrid s vw) ∂((vecLaw G).prod (vecLaw G))) = ∫ v, f v ∂vecLaw G := by
  have h := measurePreserving_hybrid G s
  have hi := integral_map h.measurable.aemeasurable (h.map_eq ▸ hf)
  rw [h.map_eq] at hi
  exact hi.symm

noncomputable def firstCoordinates {m : ℕ} (t : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun k => k.val < t)

lemma firstCoordinates_zero {m : ℕ} : firstCoordinates (m := m) 0 = ∅ := by
  ext k
  simp [firstCoordinates]

lemma firstCoordinates_full (m : ℕ) : firstCoordinates (m := m) m = Finset.univ := by
  ext k
  simp [firstCoordinates, k.isLt]

lemma hybrid_step_deleted {m : ℕ} (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) (j : Fin m) :
    Function.update (hybrid (firstCoordinates j.val) vw) j 0 =
      Function.update (hybrid (firstCoordinates (j.val + 1)) vw) j 0 := by
  classical
  funext k
  by_cases hk : k = j
  · subst k; simp
  · have hval : k.val ≠ j.val := fun h => hk (Fin.ext h)
    simp only [Function.update_of_ne hk, hybrid, firstCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and]
    have he : k.val < j.val ↔ k.val < j.val + 1 := by omega
    simp only [he]

lemma hybrid_singleton {m : ℕ} (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) (j : Fin m) :
    hybrid {j} vw = Function.update vw.2 j (vw.1 j) := by
  classical
  funext k
  by_cases hk : k = j
  · subst k; simp [hybrid]
  · simp [hybrid, hk, Function.update_of_ne hk]

lemma measurable_update_integral {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (j : Fin m) (f : (Fin m → ℝ≥0) → ℝ) (hf : Measurable f) :
    Measurable (fun z : ℝ≥0 => ∫ w, f (Function.update w j z) ∂vecLaw G) := by
  have h : Measurable (fun zw : ℝ≥0 × (Fin m → ℝ≥0) =>
      f (Function.update zw.2 j zw.1)) := hf.comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma integral_coordinate_update {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (j : Fin m) (f : (Fin m → ℝ≥0) → ℝ) (hf : Measurable f)
    (hfi : Integrable f (vecLaw G)) :
    (∫ z, ∫ w, f (Function.update w j z) ∂vecLaw G ∂(G j : Measure ℝ≥0)) =
      ∫ v, f v ∂vecLaw G := by
  have hprod : Integrable (fun vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0) =>
      f (Function.update vw.2 j (vw.1 j))) ((vecLaw G).prod (vecLaw G)) := by
    simpa only [Function.comp_def, hybrid_singleton] using
      (measurePreserving_hybrid G {j}).integrable_comp_of_integrable hfi
  calc
    _ = ∫ v, ∫ w, f (Function.update w j (v j)) ∂vecLaw G ∂vecLaw G := by
      exact (integral_comp_eval (μ := fun k => (G k : Measure ℝ≥0)) (i := j)
        (measurable_update_integral G j f hf).aestronglyMeasurable).symm
    _ = ∫ vw, f (Function.update vw.2 j (vw.1 j)) ∂((vecLaw G).prod (vecLaw G)) :=
      (integral_prod _ hprod).symm
    _ = ∫ vw, f (hybrid {j} vw) ∂((vecLaw G).prod (vecLaw G)) := by
      simp_rw [hybrid_singleton]
    _ = _ := integral_hybrid G {j} f hfi.aestronglyMeasurable

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma weighted_sum_update {m : ℕ} (a : Fin m → ℝ) (w : Fin m → ℝ≥0)
    (j : Fin m) (z : ℝ≥0) :
    (∑ k, a k * (Function.update w j z k : ℝ)) =
      (∑ k, a k * (w k : ℝ)) + a j * ((z : ℝ) - w j) := by
  classical
  have h1 := Finset.sum_erase_add Finset.univ
    (fun k => a k * (Function.update w j z k : ℝ)) (Finset.mem_univ j)
  have h2 := Finset.sum_erase_add Finset.univ (fun k => a k * (w k : ℝ)) (Finset.mem_univ j)
  have he : (∑ k ∈ Finset.univ.erase j, a k * (Function.update w j z k : ℝ)) =
      ∑ k ∈ Finset.univ.erase j, a k * (w k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he] at h1
  simp only [Function.update_self] at h1
  linarith

noncomputable def sliceAllocation {m : ℕ} (M : Mechanism (Fin m)) (j : Fin m)
    (w : Fin m → ℝ≥0) (z : ℝ≥0) : ℝ := M.q (Function.update w j z) j

noncomputable def sliceLoss {m : ℕ} (M : Mechanism (Fin m)) (j : Fin m)
    (w : Fin m → ℝ≥0) (z : ℝ≥0) : ℝ :=
  buyerPayoff M (Function.update w j z) - buyerPayoff M (Function.update w j 0)

noncomputable def slicePayment {m : ℕ} (M : Mechanism (Fin m)) (j : Fin m)
    (w : Fin m → ℝ≥0) (z : ℝ≥0) : ℝ := (z : ℝ) * sliceAllocation M j w z - sliceLoss M j w z

lemma slice_incentive {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) (w : Fin m → ℝ≥0) (z z' : ℝ≥0) :
    (z : ℝ) * sliceAllocation M j w z' - slicePayment M j w z' ≤ sliceLoss M j w z := by
  have h := hM.2.1 (Function.update w j z) (Function.update w j z')
  have he : Function.update w j z = Function.update (Function.update w j z') j z := by
    simp
  rw [he, weighted_sum_update] at h
  simp only [Function.update_self] at h
  unfold slicePayment sliceLoss sliceAllocation
  unfold buyerPayoff at h ⊢
  simp only [Function.update_idem] at h
  nlinarith

lemma sliceLoss_nonneg {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) (w : Fin m → ℝ≥0) (z : ℝ≥0) : 0 ≤ sliceLoss M j w z := by
  have h := deleted_payoff_le M hM (Function.update w j z) j
  simpa only [sliceLoss, sub_nonneg, Function.update_idem] using h

lemma slicePayment_bounds {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) (w : Fin m → ℝ≥0) (z : ℝ≥0) :
    0 ≤ slicePayment M j w z ∧ slicePayment M j w z ≤ z := by
  have hIC := slice_incentive M hM j w 0 z
  have hl0 : sliceLoss M j w 0 = 0 := by simp [sliceLoss]
  have hl := sliceLoss_nonneg M hM j w z
  have ha := hM.1 (Function.update w j z) j
  have hz := (z : ℝ≥0).coe_nonneg
  have hmul : (z : ℝ) * sliceAllocation M j w z ≤ z :=
    mul_le_of_le_one_right hz ha.2
  rw [hl0] at hIC
  simp only [NNReal.coe_zero, zero_mul, zero_sub] at hIC
  unfold slicePayment at hIC
  unfold slicePayment
  exact ⟨by linarith, by linarith⟩

lemma measurable_sliceAllocation {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Measurable (fun zw : ℝ≥0 × (Fin m → ℝ≥0) => sliceAllocation M j zw.2 zw.1) := by
  exact (hM.2.2.2.2.1 j).comp (by fun_prop)

lemma measurable_sliceLoss {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Measurable (fun zw : ℝ≥0 × (Fin m → ℝ≥0) => sliceLoss M j zw.2 zw.1) := by
  unfold sliceLoss
  exact ((measurable_payoff M hM.2.2.2.2).comp (by fun_prop)).sub
    ((measurable_payoff M hM.2.2.2.2).comp (by fun_prop))

lemma measurable_slicePayment {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Measurable (fun zw : ℝ≥0 × (Fin m → ℝ≥0) => slicePayment M j zw.2 zw.1) := by
  unfold slicePayment
  exact ((show Measurable (fun zw : ℝ≥0 × (Fin m → ℝ≥0) => (zw.1 : ℝ)) by fun_prop).mul
    (measurable_sliceAllocation M hM j)).sub (measurable_sliceLoss M hM j)

lemma integrable_sliceAllocation {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) (z : ℝ≥0) :
    Integrable (fun w => sliceAllocation M j w z) (vecLaw G) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_sliceAllocation M hM j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with w
  change |M.q (Function.update w j z) j| ≤ 1
  rw [abs_of_nonneg (hM.1 (Function.update w j z) j).1]
  exact (hM.1 (Function.update w j z) j).2

lemma integrable_slicePayment {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) (z : ℝ≥0) :
    Integrable (fun w => slicePayment M j w z) (vecLaw G) := by
  apply Integrable.mono' (integrable_const (z : ℝ))
    (((measurable_slicePayment M hM j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with w
  change |slicePayment M j w z| ≤ z
  rw [abs_of_nonneg (slicePayment_bounds M hM j w z).1]
  exact (slicePayment_bounds M hM j w z).2

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

noncomputable def averagedSlice {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (j : Fin m) : SDMechanism where
  a z := ∫ w, sliceAllocation M j w z ∂vecLaw G
  τ z := ∫ w, slicePayment M j w z ∂vecLaw G

lemma averagedSlice_payoff {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) (z : ℝ≥0) :
    (z : ℝ) * (averagedSlice G M j).a z - (averagedSlice G M j).τ z =
      ∫ w, sliceLoss M j w z ∂vecLaw G := by
  change (z : ℝ) * (∫ w, sliceAllocation M j w z ∂vecLaw G) -
    (∫ w, slicePayment M j w z ∂vecLaw G) = _
  rw [← integral_const_mul, ← integral_sub
    ((integrable_sliceAllocation G M hM j z).const_mul _) (integrable_slicePayment G M hM j z)]
  apply integral_congr_ae
  filter_upwards [] with w
  unfold slicePayment
  ring

lemma averagedSlice_admissible {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) :
    (averagedSlice G M j).IsAdmissible := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    refine ⟨integral_nonneg (fun w => (hM.1 (Function.update w j z) j).1), ?_⟩
    have h := integral_mono (integrable_sliceAllocation G M hM j z)
      (integrable_const (1 : ℝ)) (fun w => (hM.1 (Function.update w j z) j).2)
    change (∫ w, sliceAllocation M j w z ∂vecLaw G) ≤ 1
    simpa only [integral_const, probReal_univ, one_smul] using h
  · intro z
    exact integral_nonneg (fun w => (slicePayment_bounds M hM j w z).1)
  · intro z z'
    rw [averagedSlice_payoff G M hM j]
    change (z : ℝ) * (∫ w, sliceAllocation M j w z' ∂vecLaw G) -
      (∫ w, slicePayment M j w z' ∂vecLaw G) ≤ _
    rw [← integral_const_mul, ← integral_sub
      ((integrable_sliceAllocation G M hM j z').const_mul _)
      (integrable_slicePayment G M hM j z')]
    have hr : Integrable (fun w => sliceLoss M j w z) (vecLaw G) := by
      have h := ((integrable_sliceAllocation G M hM j z).const_mul (z : ℝ)).sub
        (integrable_slicePayment G M hM j z)
      convert h using 1
      funext w
      simp [slicePayment]
    exact integral_mono
      (((integrable_sliceAllocation G M hM j z').const_mul (z : ℝ)).sub
        (integrable_slicePayment G M hM j z')) hr (slice_incentive M hM j · z z')
  · intro z
    rw [averagedSlice_payoff G M hM j]
    exact integral_nonneg (sliceLoss_nonneg M hM j · z)
  · exact (measurable_sliceAllocation M hM j).stronglyMeasurable.integral_prod_right'.measurable
  · exact (measurable_slicePayment M hM j).stronglyMeasurable.integral_prod_right'.measurable

lemma averagedSlice_alloc {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) (j : Fin m) :
    (averagedSlice G M j).alloc (G j) = qAlloc (vecLaw G) M j := by
  exact integral_coordinate_update G j (fun v => M.q v j) (hM.2.2.2.2.1 j)
    (integrable_allocation G M hM j)

lemma measurable_deletionComponent {m : ℕ} (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : Measurable (deletionComponent M j) := by
  unfold deletionComponent
  exact (measurable_payoff M hM.2.2.2.2).sub
    ((measurable_payoff M hM.2.2.2.2).comp (by fun_prop))

lemma averagedSlice_utility {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (j : Fin m) : (averagedSlice G M j).utility (G j) = deletionLoss (vecLaw G) M j := by
  unfold SDMechanism.utility
  simp_rw [averagedSlice_payoff G M hM j]
  have he (w : Fin m → ℝ≥0) (z : ℝ≥0) :
      sliceLoss M j w z = deletionComponent M j (Function.update w j z) := by
    simp [sliceLoss, deletionComponent, Function.update_idem]
  simp_rw [he]
  exact integral_coordinate_update G j (deletionComponent M j) (measurable_deletionComponent M hM j)
    (integrable_deletionComponent G hG M hM j)

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma single_utility_le_mean (ν : ProbabilityMeasure ℝ≥0) (hν : HasFiniteMean ν)
    (M : SDMechanism) (hM : M.IsAdmissible) : M.utility ν ≤ mean ν := by
  have hb (z : ℝ≥0) : 0 ≤ (z : ℝ) * M.a z - M.τ z ∧
      (z : ℝ) * M.a z - M.τ z ≤ z := by
    refine ⟨hM.2.2.2.1 z, ?_⟩
    have hh := mul_le_of_le_one_right z.coe_nonneg (hM.1 z).2
    linarith [hM.2.1 z]
  have hm : Measurable (fun z : ℝ≥0 => (z : ℝ) * M.a z - M.τ z) :=
    ((show Measurable (fun z : ℝ≥0 => (z : ℝ)) by fun_prop).mul hM.2.2.2.2.1).sub hM.2.2.2.2.2
  have hi : Integrable (fun z : ℝ≥0 => (z : ℝ) * M.a z - M.τ z) (ν : Measure ℝ≥0) := by
    apply Integrable.mono' hν hm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]
    exact (hb z).2
  exact integral_mono hi hν (fun z => (hb z).2)

theorem lemma_2 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j) (j : Fin m) :
    deletionLoss (vecLaw G) M j ≤ OPT11 (G j) (q j) := by
  have hb : BddAbove {u : ℝ | ∃ S : SDMechanism,
      S.IsAdmissible ∧ S.alloc (G j) ≤ q j ∧ S.utility (G j) = u} := by
    refine ⟨mean (G j), ?_⟩
    rintro u ⟨S, hS, hqS, rfl⟩
    exact single_utility_le_mean (G j) (hG j).1 S hS
  apply le_csSup hb
  exact ⟨averagedSlice G M j, averagedSlice_admissible G M hM j,
    by rw [averagedSlice_alloc G M hM j]; exact hq j,
    averagedSlice_utility G hG M hM j⟩

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.PricingProof

noncomputable section

lemma alpha_nonneg : 0 ≤ 1 - Real.exp (-1) := by
  have h := Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  simpa using sub_nonneg.mpr h

lemma alpha_cap_constant :
    (1 - Real.exp (-1)) * (Real.exp 1 / (Real.exp 1 - 1)) = 1 := by
  have he : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have he1 : Real.exp 1 - 1 ≠ 0 := by
    have hh := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    linarith
  rw [Real.exp_neg]
  field_simp
  <;> ring

lemma OPT11_nonempty (ν : ProbabilityMeasure ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    {u : ℝ | ∃ M : SDMechanism,
      M.IsAdmissible ∧ M.alloc ν ≤ q ∧ M.utility ν = u}.Nonempty := by
  let M : SDMechanism := ⟨fun _ => 0, fun _ => 0⟩
  refine ⟨0, M, ?_, ?_, ?_⟩
  · exact ⟨by simp [M], by simp [M], by simp [M], by simp [M],
      measurable_const, measurable_const⟩
  · simpa [SDMechanism.alloc, M] using hq
  · simp [SDMechanism.utility, M]

lemma OPT11_le_mean (ν : ProbabilityMeasure ℝ≥0) (hν : HasFiniteMean ν)
    (q : ℝ) (hq : 0 ≤ q) : OPT11 ν q ≤ mean ν := by
  apply csSup_le (OPT11_nonempty ν q hq)
  rintro u ⟨M, hM, _, rfl⟩
  exact BenchmarkProof.single_utility_le_mean ν hν M hM

lemma comparison_caps_feasible {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) (hUD : IsUnitDemand C) :
    IsFeasibleCaps (qAlloc (vecLaw G) C) := by
  constructor
  · intro j
    exact integral_nonneg (fun v => (hC.1 v j).1)
  · unfold qAlloc
    rw [← integral_finsetSum Finset.univ
      (fun j _ => BenchmarkProof.integrable_allocation G C hC j)]
    calc
      _ ≤ ∫ _ : Fin m → ℝ≥0, (1 : ℝ) ∂vecLaw G :=
        integral_mono (integrable_finsetSum Finset.univ
          (fun j _ => BenchmarkProof.integrable_allocation G C hC j))
          (integrable_const 1) hUD
      _ = 1 := by simp

lemma capObjective_bddAbove {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j) :
    BddAbove {r : ℝ | ∃ q, IsFeasibleCaps q ∧ capObjective G lam q = r} := by
  refine ⟨∑ j, mean (G j), ?_⟩
  rintro r ⟨q, hq, rfl⟩
  apply Finset.sum_le_sum
  intro j _
  have hp : 0 ≤ Real.exp 1 / (Real.exp 1 - 1) * lam j * q j := by
    have he : 0 ≤ Real.exp 1 / (Real.exp 1 - 1) := by
      apply div_nonneg (le_of_lt (Real.exp_pos 1))
      have hh := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
      linarith
    exact mul_nonneg (mul_nonneg he (hlam j)) (hq.1 j)
  exact (sub_le_self _ hp).trans (OPT11_le_mean (G j) (hG j).1 (q j) (hq.1 j))

lemma capObjective_le_capOpt {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (q : Fin m → ℝ) (hq : IsFeasibleCaps q) :
    capObjective G lam q ≤ capOpt G lam := by
  exact le_csSup (capObjective_bddAbove G hG lam hlam) ⟨q, hq, rfl⟩

lemma alpha_capObjective {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (lam q : Fin m → ℝ) :
    (1 - Real.exp (-1)) * capObjective G lam q =
      (1 - Real.exp (-1)) * (∑ j, OPT11 (G j) (q j)) - ∑ j, lam j * q j := by
  unfold capObjective
  simp_rw [Finset.mul_sum, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ((1 - Real.exp (-1)) * (Real.exp 1 / (Real.exp 1 - 1))) *
        (lam j * q j) := by ring
    _ = _ := by rw [alpha_cap_constant, one_mul]

lemma comparison_capObjective {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (lam : Fin m → ℝ) (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) :
    (1 - Real.exp (-1)) * totalDeletionLoss (vecLaw G) C -
        ∑ j, lam j * qAlloc (vecLaw G) C j ≤
      (1 - Real.exp (-1)) * capObjective G lam (qAlloc (vecLaw G) C) := by
  rw [alpha_capObjective]
  apply sub_le_sub_right
  apply mul_le_mul_of_nonneg_left _ alpha_nonneg
  apply Finset.sum_le_sum
  intro j _
  exact BenchmarkProof.lemma_2 hm G hG C hC (qAlloc (vecLaw G) C) (fun _ => le_rfl) j

/-- The cap program already implies the comparison bound for the paper's genuine
independent-price measures. No existence of an optimizing cap is assumed. -/
theorem pricing_measure_benchmark {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (caps : Fin m → ℝ) (hcaps : IsFeasibleCaps caps) (δ : ℝ)
    (hopt : capOpt G lam - δ ≤ capObjective G lam caps)
    (pr : Fin m → TwoPointPrice) (hpr : ∀ j, IsImplementing (G j) (caps j) (pr j))
    (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) (hUD : IsUnitDemand C) :
    (1 - Real.exp (-1)) * totalDeletionLoss (vecLaw G) C -
        (∑ j, lam j * qAlloc (vecLaw G) C j) - (1 - Real.exp (-1)) * δ ≤
      udUtility G (fun j => (pr j).law.toMeasure) -
        ∑ j, lam j * udAlloc G (fun j => (pr j).law.toMeasure) j := by
  have hp := SurplusProof.lemma_3 hm G hG (fun j => (pr j).law.toMeasure) caps
    (fun j => (hpr j).1) hcaps.2
  have hu : (1 - Real.exp (-1)) * (∑ j, OPT11 (G j) (caps j)) ≤
      udUtility G (fun j => (pr j).law.toMeasure) := by
    simpa only [fun j => (hpr j).2] using hp.2
  have ha : (∑ j, lam j * udAlloc G (fun j => (pr j).law.toMeasure) j) ≤
      ∑ j, lam j * caps j := by
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hp.1 j) (hlam j))
  have hh := mul_le_mul_of_nonneg_left hopt alpha_nonneg
  have hc := mul_le_mul_of_nonneg_left
    (capObjective_le_capOpt G hG lam hlam (qAlloc (vecLaw G) C)
      (comparison_caps_feasible G C hC hUD)) alpha_nonneg
  have hd := comparison_capObjective hm G hG lam C hC
  rw [alpha_capObjective G lam caps] at hh
  linarith

end
end Utility7.PricingProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma indep_map {α β : Type} (n : ℕ) (p : Fin n → PMF α) (f : Fin n → α → β) :
    (indep n p).map (fun a i => f i (a i)) = indep n (fun i => (p i).map (f i)) := by
  induction n with
  | zero =>
    simp only [indep, PMF.pure_map]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [indep, PMF.map_bind, PMF.bind_map, PMF.map_comp]
    congr 1
    funext a
    calc
      _ = ((indep n (fun i => p i.succ)).map
          (fun g i => f i.succ (g i))).map (fun g => Fin.cons (f 0 a) g) := by
        rw [PMF.map_comp]
        congr 1
        funext g i
        induction i using Fin.cases <;> rfl
      _ = _ := by rw [ih]; rfl

noncomputable def boolSet {n : ℕ} (b : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i = true)

lemma boolSet_injective {n : ℕ} : Function.Injective (@boolSet n) := by
  intro a b h
  funext i
  have hh : a i = true ↔ b i = true := by
    simpa only [boolSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.ext_iff.mp h i)
  cases ha : a i <;> cases hb : b i <;> simp_all

lemma boolSet_decide {n : ℕ} (A : Finset (Fin n)) :
    boolSet (fun i => decide (i ∈ A)) = A := by
  ext i
  simp [boolSet]

lemma indep_boolSet_apply {n : ℕ} (p : Fin n → PMF Bool) (A : Finset (Fin n)) :
    ((indep n p).map boolSet) A = ∏ i, if i ∈ A then p i true else p i false := by
  have hA : A = boolSet (fun i => decide (i ∈ A)) := (boolSet_decide A).symm
  rw [hA, PMF.map_apply]
  simp_rw [boolSet_injective.eq_iff]
  simp only [tsum_ite_eq, tsum_ite_eq']
  rw [indep_apply]
  apply Finset.prod_congr rfl
  intro i _
  simp only [boolSet_decide]
  by_cases hi : i ∈ A <;> simp [hi]

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.PricingProof

noncomputable section

lemma indep_bool_toMeasure {m : ℕ} (p : Fin m → PMF Bool) :
    (indep m p).toMeasure = Measure.pi (fun j => (p j).toMeasure) := by
  apply Measure.ext_of_singleton
  intro t
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact ContentionProof.indep_apply m p t

/-- The price vector used by the actual randomized mechanism has exactly the
product of the published two-point marginal measures. -/
lemma price_vector_toMeasure {m : ℕ} (pr : Fin m → TwoPointPrice) :
    (indep m (fun j => (pr j).law)).toMeasure =
      Measure.pi (fun j => (pr j).law.toMeasure) := by
  let p : Fin m → PMF Bool := fun j => coin (pr j).θ
  let f : Fin m → Bool → ℝ≥0∞ := fun j b => if b then (pr j).p₁ else (pr j).p₂
  have hf (j : Fin m) : Measurable (f j) := measurable_of_countable _
  have hF : Measurable (fun a : Fin m → Bool => fun j => f j (a j)) :=
    measurable_pi_lambda _ (fun j => (hf j).comp (measurable_pi_apply j))
  change (indep m (fun j => (p j).map (f j))).toMeasure = _
  rw [← ContentionProof.indep_map m p f, ← PMF.toMeasure_map _ _ hF,
    indep_bool_toMeasure]
  rw [Measure.pi_map_pi (fun j => (hf j).aemeasurable)]
  simp_rw [PMF.toMeasure_map _ _ (hf _)]
  rfl

end
end Utility7.PricingProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.PricingProof

noncomputable section
open ContentionProof SurplusProof

lemma price_choice_integrable_measure {m : ℕ}
    (v : Fin m → ℝ≥0) (j : Fin m)
    (μ : Measure (Fin m → ℝ≥0∞)) [IsFiniteMeasure μ] :
    Integrable (fun t => udChoice v t j) μ := by
  have hp : Measurable (fun t : Fin m → ℝ≥0∞ =>
      fun k : Fin m => ((t k, v k) : PriceValue)) :=
    measurable_pi_lambda _ (fun k => (measurable_pi_apply k).prodMk measurable_const)
  have hm : Measurable (fun t : Fin m → ℝ≥0∞ => udChoice v t j) := by
    simpa only [Function.comp_def] using (jointChoice_measurable j).comp hp
  apply (integrable_const (μ := μ) (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_nonneg (choice_bounds v t j).1]
  exact (choice_bounds v t j).2

lemma price_choice_integrable {m : ℕ} (pr : Fin m → TwoPointPrice)
    (v : Fin m → ℝ≥0) (j : Fin m) :
    Integrable (fun t => udChoice v t j) (indep m (fun j => (pr j).law)).toMeasure :=
  price_choice_integrable_measure v j _

lemma postedPrice_allocation_integral {m : ℕ} (pr : Fin m → TwoPointPrice)
    (v : Fin m → ℝ≥0) (j : Fin m) :
    (postedPriceMech pr).alloc v j =
      ∫ t, udChoice v t j ∂Measure.pi (fun k => (pr k).law.toMeasure) := by
  rw [postedPrice_as_mixture, mixture_allocation]
  simp_rw [fixedPrice_allocation, uniformOn_some_probability]
  rw [← price_vector_toMeasure pr]
  exact (PMF.integral_eq_tsum _ _ (price_choice_integrable pr v j)).symm

lemma price_maximum_integrable {m : ℕ} [Nonempty (Fin m)]
    (pr : Fin m → TwoPointPrice) (v : Fin m → ℝ≥0) :
    Integrable (fun t => maximum (fun j (_ : Unit) => surplus (v j) (t j)) ())
      (indep m (fun j => (pr j).law)).toMeasure := by
  have hm (j : Fin m) : Measurable (fun t : Fin m → ℝ≥0∞ => surplus (v j) (t j)) := by
    have hp : Measurable (fun t : Fin m → ℝ≥0∞ => ((t j, v j) : PriceValue)) :=
      (measurable_pi_apply j).prodMk measurable_const
    exact measurable_surplus.comp hp
  have hi (j : Fin m) : Integrable (fun t : Fin m → ℝ≥0∞ => surplus (v j) (t j))
      (indep m (fun j => (pr j).law)).toMeasure := by
    apply (integrable_const (v j : ℝ)).mono' (hm j).aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (surplus_nonneg _ _)]
    exact surplus_le_value _ _
  exact maximum_integrable _ hm hi (fun _ _ => surplus_nonneg _ _)

lemma postedPrice_payoff_integral {m : ℕ} [Nonempty (Fin m)]
    (pr : Fin m → TwoPointPrice) (v : Fin m → ℝ≥0) :
    buyerPayoff (postedPriceMech pr).reduced v =
      ∫ t, maximum (fun j (_ : Unit) => surplus (v j) (t j)) ()
        ∂Measure.pi (fun j => (pr j).law.toMeasure) := by
  change reportUtility (postedPriceMech pr) v v = _
  rw [postedPrice_as_mixture, mixture_reportUtility _ _
    (fun t _ => (fixedPrice_safety t).1) (fun t _ => (fixedPrice_safety t).2)]
  simp_rw [show ∀ t : Fin m → ℝ≥0∞, reportUtility (fixedPriceMech t) v v =
      maximum (fun j (_ : Unit) => surplus (v j) (t j)) () from
    fun t => fixedPrice_truthful_utility t v]
  rw [← price_vector_toMeasure pr]
  exact (PMF.integral_eq_tsum _ _ (price_maximum_integrable pr v)).symm

theorem qAlloc_postedPrice {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (pr : Fin m → TwoPointPrice) (j : Fin m) :
    qAlloc (vecLaw G) (postedPriceMech pr).reduced j =
      udAlloc G (fun j => (pr j).law.toMeasure) j := by
  let π : Fin m → Measure ℝ≥0∞ := fun j => (pr j).law.toMeasure
  have hi := (joint_integrable_iff G π (fun z => udChoice z.2 z.1 j)).mp
    (jointChoice_integrable G π j)
  change (∫ v, (postedPriceMech pr).alloc v j ∂vecLaw G) = _
  simp_rw [postedPrice_allocation_integral]
  exact (integral_integral_swap hi).symm

theorem utility_postedPrice {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (pr : Fin m → TwoPointPrice) :
    utility (vecLaw G) (postedPriceMech pr).reduced =
      udUtility G (fun j => (pr j).law.toMeasure) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let π : Fin m → Measure ℝ≥0∞ := fun j => (pr j).law.toMeasure
  let F : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) → ℝ :=
    fun z => maximum (fun j (_ : Unit) => surplus (z.2 j) (z.1 j)) ()
  have hi := maximum_integrable (jointSurplus : Fin m → (Fin m → PriceValue) → ℝ)
    jointSurplus_measurable (jointSurplus_integrable G π (fun j => (hG j).1))
    (fun _ _ => surplus_nonneg _ _)
  have hF : Integrable F ((Measure.pi π).prod (vecLaw G)) :=
    (joint_integrable_iff G π F).mp hi
  unfold utility
  simp_rw [postedPrice_payoff_integral]
  calc
    _ = ∫ t, ∫ v, maximum (fun j (_ : Unit) => surplus (v j) (t j)) ()
        ∂vecLaw G ∂Measure.pi π := (integral_integral_swap hF).symm
    _ = udUtility G π := by
      unfold udUtility
      apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with v
      exact (choice_utility_maximum v t).symm

end
end Utility7.PricingProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.PricingProof

/-- The pricing branch uses the actual randomized posted-price mechanism, with
its original allocation and payment rules. -/
theorem pricing_benchmark {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (caps : Fin m → ℝ) (hcaps : IsFeasibleCaps caps) (δ : ℝ)
    (hopt : capOpt G lam - δ ≤ capObjective G lam caps)
    (pr : Fin m → TwoPointPrice) (hpr : ∀ j, IsImplementing (G j) (caps j) (pr j))
    (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) (hUD : IsUnitDemand C) :
    (1 - Real.exp (-1)) * totalDeletionLoss (vecLaw G) C -
        (∑ j, lam j * qAlloc (vecLaw G) C j) - (1 - Real.exp (-1)) * δ ≤
      utility (vecLaw G) (postedPriceMech pr).reduced -
        ∑ j, lam j * qAlloc (vecLaw G) (postedPriceMech pr).reduced j := by
  rw [utility_postedPrice hm G hG pr]
  simp_rw [qAlloc_postedPrice G pr]
  exact pricing_measure_benchmark hm G hG lam hlam caps hcaps δ hopt pr hpr C hC hUD

theorem postedPrice_caps {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (caps : Fin m → ℝ) (hcaps : IsFeasibleCaps caps)
    (pr : Fin m → TwoPointPrice) (hpr : ∀ j, IsImplementing (G j) (caps j) (pr j)) :
    ∀ j, qAlloc (vecLaw G) (postedPriceMech pr).reduced j ≤ caps j := by
  intro j
  rw [qAlloc_postedPrice G pr]
  exact (SurplusProof.lemma_3 hm G hG (fun j => (pr j).law.toMeasure) caps
    (fun j => (hpr j).1) hcaps.2).1 j

end Utility7.PricingProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma measurable_udCandidates {m : ℕ} (t : Fin m → ℝ≥0∞) :
    Measurable (fun v : Fin m → ℝ≥0 => udCandidates v t) := by
  apply measurable_finset_iff.mpr
  intro j
  apply measurableSet_setOfPred.mp
  simp only [udCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  have hs : ∀ j, Measurable (fun v : Fin m → ℝ≥0 => surplus (v j) (t j)) := by
    intro j
    unfold surplus
    split_ifs
    · exact measurable_const
    · fun_prop
  have hm : MeasurableSet {v : Fin m → ℝ≥0 |
      ∀ k, surplus (v k) (t k) ≤ surplus (v j) (t j)} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le (hs k) (hs j))
  exact (measurableSet_lt measurable_const (hs j)).inter hm

lemma measurable_fixedPrice_alloc {m : ℕ} (t : Fin m → ℝ≥0∞) (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (fixedPriceMech t).alloc v j) := by
  simp_rw [fixedPrice_allocation]
  exact (measurable_of_countable (fun S : Finset (Fin m) =>
    ((ConsumerUtilityApprox.UnitDemand.uniformOn S) (some j)).toReal)).comp
      (measurable_udCandidates t)

lemma mixture_allocation_finite {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (s : Finset α) (hs : ∀ a ∈ p.support, a ∈ s) (v : Fin m → ℝ≥0) (j : Fin m) :
    (mixture p M).alloc v j = ∑ a ∈ s, (p a).toReal * (M a).alloc v j := by
  rw [mixture_allocation]
  apply tsum_eq_sum
  intro a ha
  have hz : p a = 0 := (p.apply_eq_zero_iff a).mpr (fun h => ha (hs a h))
  simp [hz]

lemma measurable_mixture_alloc {α : Type} {m : ℕ} (p : PMF α) (M : α → SBRand m)
    (s : Finset α) (hs : ∀ a ∈ p.support, a ∈ s) (j : Fin m)
    (hM : ∀ a ∈ s, Measurable (fun v : Fin m → ℝ≥0 => (M a).alloc v j)) :
    Measurable (fun v : Fin m → ℝ≥0 => (mixture p M).alloc v j) := by
  simp_rw [mixture_allocation_finite p M s hs]
  exact Finset.measurable_sum s (fun a ha => (hM a ha).const_mul _)

noncomputable def priceOptions {m : ℕ} (pr : Fin m → TwoPointPrice) :
    Finset (Fin m → ℝ≥0∞) := Fintype.piFinset (fun j => {(pr j).p₁, (pr j).p₂})

lemma priceOptions_support {m : ℕ} (pr : Fin m → TwoPointPrice)
    (t : Fin m → ℝ≥0∞) (ht : t ∈ (indep m (fun j => (pr j).law)).support) :
    t ∈ priceOptions pr := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj := indep_support_coordinate _ _ ht j
  unfold TwoPointPrice.law at hj
  obtain ⟨b, hb, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hj
  cases b <;> simp_all

lemma measurable_postedPrice_alloc {m : ℕ} (pr : Fin m → TwoPointPrice) (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (postedPriceMech pr).alloc v j) := by
  rw [postedPrice_as_mixture]
  exact measurable_mixture_alloc _ _ (priceOptions pr) (priceOptions_support pr) j
    (fun t _ => measurable_fixedPrice_alloc t j)

lemma measurable_null_alloc {m : ℕ} (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (nullMech : SBRand m).alloc v j) := by
  unfold SBRand.alloc nullMech
  exact measurable_const

lemma measurable_round_alloc {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (t : ℕ) (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (roundMech D i t).alloc v j) := by
  unfold roundMech
  apply measurable_mixture_alloc _ _ Finset.univ (by simp)
  intro b _
  cases b
  · exact ConsumerUtilityApprox.UnitDemand.OGDProof.measurable_freeLottery_alloc _ j
  · exact measurable_postedPrice_alloc _ j

lemma measurable_participate_alloc {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (hT : (Finset.range D.T).Nonempty) (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (participateMech D i hT).alloc v j) := by
  unfold participateMech
  apply measurable_mixture_alloc _ _ (Finset.range D.T)
    (fun t ht => (PMF.mem_support_uniformOfFinset_iff _ _).mp ht)
  exact fun t _ => measurable_round_alloc D i t j

theorem measurable_request_alloc {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) :
    Measurable (fun v : Fin m → ℝ≥0 => (requestMech D i).alloc v j) := by
  rw [request_as_mixtures]
  split_ifs with hT
  · apply measurable_mixture_alloc _ _ Finset.univ (by simp)
    intro b _
    cases b
    · exact measurable_null_alloc j
    · exact measurable_participate_alloc D i hT j
  · exact measurable_null_alloc j

theorem integrable_request_alloc {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (μ : Measure (Fin m → ℝ≥0)) [IsFiniteMeasure μ] :
    Integrable (fun v => (requestMech D i).alloc v j) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_request_alloc D i j).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg
    (ConsumerUtilityApprox.UnitDemand.OGDProof.alloc_mem_unit_interval _ _ _).1]
  exact (ConsumerUtilityApprox.UnitDemand.OGDProof.alloc_mem_unit_interval _ _ _).2

lemma announced_eq_request_mean {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j) (i : Fin n) (j : Fin m) :
    D.Q i j = ∫ v, (requestMech D i).alloc v j ∂I.buyerLaw i := by
  rw [hQ]
  unfold RMech.exAnteAlloc
  simp_rw [preLaw_allocation]
  change (∫ v, (requestMech D i).alloc (v i) j ∂Measure.pi (fun k => I.buyerLaw k)) = _
  exact integral_comp_eval (μ := fun k => I.buyerLaw k)
    (i := i) (measurable_request_alloc D i j).aestronglyMeasurable

end Utility7.ContentionProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.PricingProof

noncomputable section
open ContentionProof SurplusProof

lemma maximum_measurable {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (maximum f) := by
  have he : maximum f = Finset.univ.sup' Finset.univ_nonempty f := by
    funext ω
    exact (Finset.sup'_apply Finset.univ_nonempty f ω).symm
  rw [he]
  exact Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hf i)

lemma postedPrice_measurable_payoff {m : ℕ} (hm : 1 ≤ m)
    (pr : Fin m → TwoPointPrice) : Measurable (buyerPayoff (postedPriceMech pr).reduced) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let F : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) → ℝ :=
    fun z => maximum (fun j (_ : Unit) => surplus (z.2 j) (z.1 j)) ()
  have hF : Measurable F := by
    apply maximum_measurable
      (fun (j : Fin m) (z : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0)) =>
        surplus (z.2 j) (z.1 j))
    intro j
    have hp : Measurable (fun z : (Fin m → ℝ≥0∞) × (Fin m → ℝ≥0) =>
        ((z.1 j, z.2 j) : PriceValue)) := by fun_prop
    exact measurable_surplus.comp hp
  have hmeas : Measurable (fun v => ∫ t, F (t, v)
      ∂Measure.pi (fun j => (pr j).law.toMeasure)) :=
    hF.stronglyMeasurable.integral_prod_left'.measurable
  have he : buyerPayoff (postedPriceMech pr).reduced =
      fun v => ∫ t, F (t, v) ∂Measure.pi (fun j => (pr j).law.toMeasure) := by
    funext v
    exact postedPrice_payoff_integral pr v
  rw [he]
  exact hmeas

lemma postedPrice_measurable_payment {m : ℕ} (hm : 1 ≤ m)
    (pr : Fin m → TwoPointPrice) : Measurable (postedPriceMech pr).pay := by
  have ha : Measurable (fun v : Fin m → ℝ≥0 =>
      ∑ j, (postedPriceMech pr).alloc v j * (v j : ℝ)) :=
    Finset.measurable_sum Finset.univ (fun j _ =>
      (measurable_postedPrice_alloc pr j).mul (by fun_prop))
  have hp := ha.sub (postedPrice_measurable_payoff hm pr)
  change Measurable (fun v : Fin m → ℝ≥0 =>
    (∑ j, (postedPriceMech pr).alloc v j * (v j : ℝ)) -
      buyerPayoff (postedPriceMech pr).reduced v) at hp
  have he : (fun v : Fin m → ℝ≥0 => (∑ j, (postedPriceMech pr).alloc v j * (v j : ℝ)) -
      buyerPayoff (postedPriceMech pr).reduced v) = (postedPriceMech pr).pay := by
    funext v
    simp only [buyerPayoff, SBRand.reduced]
    ring
  rwa [he] at hp

lemma postedPrice_integrable_allocation {m : ℕ} (pr : Fin m → TwoPointPrice)
    (μ : Measure (Fin m → ℝ≥0)) [IsFiniteMeasure μ] (j : Fin m) :
    Integrable (fun v => (postedPriceMech pr).alloc v j) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    (measurable_postedPrice_alloc pr j).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_nonneg (OGDProof.alloc_mem_unit_interval _ _ _).1]
  exact (OGDProof.alloc_mem_unit_interval _ _ _).2

lemma postedPrice_integrable_payment {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (pr : Fin m → TwoPointPrice) : Integrable (postedPriceMech pr).pay (vecLaw G) := by
  have hb (v : Fin m → ℝ≥0) := payment_bounds (postedPriceMech pr)
    (postedPrice_safety pr).1 (postedPrice_safety pr).2 v
  apply (integrable_finsetSum Finset.univ
    (fun j _ => BenchmarkProof.integrable_value G hG j)).mono'
      (postedPrice_measurable_payment hm pr).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_eq_abs, abs_of_nonneg (hb v).1]
  exact (hb v).2

lemma postedPrice_integrable_payoff {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (pr : Fin m → TwoPointPrice) :
    Integrable (buyerPayoff (postedPriceMech pr).reduced) (vecLaw G) := by
  have ha (j : Fin m) : Integrable (fun v : Fin m → ℝ≥0 =>
      (postedPriceMech pr).alloc v j * (v j : ℝ)) (vecLaw G) := by
    have hmeas : Measurable (fun v : Fin m → ℝ≥0 =>
        (postedPriceMech pr).alloc v j * (v j : ℝ)) := (measurable_postedPrice_alloc pr j).mul
      (show Measurable (fun v : Fin m → ℝ≥0 => (v j : ℝ)) by fun_prop)
    apply (BenchmarkProof.integrable_value G hG j).mono' hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro v
    have hb := OGDProof.alloc_mem_unit_interval (postedPriceMech pr) v j
    change ‖(postedPriceMech pr).alloc v j * (v j : ℝ)‖ ≤ (v j : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb.1 (v j).coe_nonneg)]
    exact mul_le_of_le_one_left (v j).coe_nonneg hb.2
  exact (integrable_finsetSum Finset.univ (fun j _ => ha j)).sub
    (postedPrice_integrable_payment hm G hG pr)

end
end Utility7.PricingProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma min_le_cross_average (u v a b c d : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hU : u ≤ a * b) (hV : v ≤ c * d) :
    min u v ≤ (a * d + c * b) / 2 := by
  have hmin : 0 ≤ min u v := le_min hu hv
  have hsq : min u v ^ 2 ≤ u * v := by
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv]
      nlinarith
    · rw [min_eq_right hvu]
      nlinarith
  have hprod : u * v ≤ (a * b) * (c * d) :=
    mul_le_mul hU hV hv (mul_nonneg ha hb)
  have hcross := sq_nonneg (a * d - c * b)
  have hsum : 0 ≤ a * d + c * b := add_nonneg (mul_nonneg ha hd) (mul_nonneg hc hb)
  nlinarith only [hsq, hprod, hcross, hsum, hmin]

theorem lemma_1 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j)
    (ell : Fin m → ℝ) (hell : ∀ j, 0 < ell j ∧ ell j ≤ 1) :
    (∫ vw, min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ∂((vecLaw G).prod (vecLaw G)))
      ≤ (∫ v, (⨆ j, ell j * (v j : ℝ)) ∂(vecLaw G)) * ∑ j, q j / ell j := by
  classical
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let a : (Fin m → ℝ≥0) → ℝ := Utility7.SurplusProof.maximum (fun j v => ell j * (v j : ℝ))
  let b : (Fin m → ℝ≥0) → ℝ := fun v => ∑ j, M.q v j / ell j
  have ha0 : ∀ v, 0 ≤ a v := Utility7.SurplusProof.maximum_nonneg _
    (fun j v => mul_nonneg (hell j).1.le (v j).coe_nonneg)
  have hb0 : ∀ v, 0 ≤ b v := fun v => Finset.sum_nonneg
    (fun j _ => div_nonneg (hM.1 v j).1 (hell j).1.le)
  have hai : Integrable a (vecLaw G) := Utility7.SurplusProof.maximum_integrable _
    (fun j => by fun_prop) (fun j => (integrable_value G hG j).const_mul _)
    (fun j v => mul_nonneg (hell j).1.le (v j).coe_nonneg)
  have hbi : Integrable b (vecLaw G) := integrable_finsetSum Finset.univ
    (fun j _ => (integrable_allocation G M hM j).div_const _)
  have hbound (v : Fin m → ℝ≥0) : buyerPayoff M v ≤ a v * b v := by
    have hs : (∑ j, M.q v j * (v j : ℝ)) ≤ a v * b v := by
      dsimp only [b]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hmax : ell j * (v j : ℝ) ≤ a v :=
        Finset.le_sup' (fun k => ell k * (v k : ℝ)) (Finset.mem_univ j)
      have hh := mul_le_mul_of_nonneg_right hmax (div_nonneg (hM.1 v j).1 (hell j).1.le)
      convert hh using 1 <;> field_simp [(hell j).1.ne'] <;> ring
    unfold buyerPayoff
    linarith [hM.2.2.2.1 v]
  have hui := integrable_payoff G hG M hM
  have hmini := (hui.comp_fst (vecLaw G)).inf (hui.comp_snd (vecLaw G))
  have hupper := ((hai.mul_prod hbi).add (hbi.mul_prod hai)).div_const 2
  have hpoint (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) :
      min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ≤
        (a vw.1 * b vw.2 + b vw.1 * a vw.2) / 2 := by
    simpa only [mul_comm] using min_le_cross_average _ _ _ _ _ _
      (payoff_bounds M hM vw.1).1 (payoff_bounds M hM vw.2).1
      (ha0 vw.1) (hb0 vw.1) (ha0 vw.2) (hb0 vw.2) (hbound vw.1) (hbound vw.2)
  have hint := integral_mono hmini hupper hpoint
  simp only [Pi.add_apply, Pi.inf_apply] at hint
  rw [integral_div, integral_add (hai.mul_prod hbi) (hbi.mul_prod hai),
    integral_prod_mul, integral_prod_mul] at hint
  have he : (∫ v, b v ∂vecLaw G) ≤ ∑ j, q j / ell j := by
    change (∫ v, ∑ j, M.q v j / ell j ∂vecLaw G) ≤ _
    rw [integral_finsetSum _ (fun j _ => (integrable_allocation G M hM j).div_const _)]
    apply Finset.sum_le_sum
    intro j _
    rw [integral_div]
    exact div_le_div_of_nonneg_right (hq j) (hell j).1.le
  have haInt : 0 ≤ ∫ v, a v ∂vecLaw G := integral_nonneg ha0
  have hfinal := mul_le_mul_of_nonneg_left he haInt
  have hae : ∀ v, a v = ⨆ j, ell j * (v j : ℝ) := fun v =>
    Finset.sup'_univ_eq_ciSup _
  simp_rw [← hae]
  nlinarith only [hint, hfinal]

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma abs_payoff_sub_le_hybrid_deletions {m : ℕ} (M : Mechanism (Fin m))
    (hM : IsTruthfulIRNPT M) (vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0)) :
    |buyerPayoff M vw.1 - buyerPayoff M vw.2| ≤
      ∑ j : Fin m, (deletionComponent M j (hybrid (firstCoordinates j.val) vw) +
        deletionComponent M j (hybrid (firstCoordinates (j.val + 1)) vw)) := by
  classical
  have ht := dist_le_range_sum_dist
    (fun t => buyerPayoff M (hybrid (firstCoordinates t) vw)) m
  simp only [firstCoordinates_zero, firstCoordinates_full, hybrid_empty, hybrid_univ,
    Real.dist_eq] at ht
  calc
    _ = |buyerPayoff M vw.2 - buyerPayoff M vw.1| := abs_sub_comm _ _
    _ ≤ ∑ t ∈ Finset.range m,
        |buyerPayoff M (hybrid (firstCoordinates t) vw) -
          buyerPayoff M (hybrid (firstCoordinates (t + 1)) vw)| := ht
    _ = ∑ j : Fin m,
        |buyerPayoff M (hybrid (firstCoordinates j.val) vw) -
          buyerPayoff M (hybrid (firstCoordinates (j.val + 1)) vw)| := by
      exact (Fin.sum_univ_eq_sum_range (fun t =>
        |buyerPayoff M (hybrid (firstCoordinates t) vw) -
          buyerPayoff M (hybrid (firstCoordinates (t + 1)) vw)|) m).symm
    _ ≤ _ := Finset.sum_le_sum (fun j _ => abs_payoff_sub_le_deletions M hM j _ _
      (hybrid_step_deleted vw j))

theorem eq_3_3 {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) :
    (1 / 2 : ℝ) * ∫ vw, |buyerPayoff M vw.1 - buyerPayoff M vw.2| ∂((vecLaw G).prod (vecLaw G))
      ≤ totalDeletionLoss (vecLaw G) M := by
  have hu := integrable_payoff G hG M hM
  have hleft := ((hu.comp_fst (vecLaw G)).sub (hu.comp_snd (vecLaw G))).abs
  have hd (j : Fin m) (t : ℕ) : Integrable
      (fun vw => deletionComponent M j (hybrid (firstCoordinates t) vw))
      ((vecLaw G).prod (vecLaw G)) :=
    (measurePreserving_hybrid G (firstCoordinates t)).integrable_comp_of_integrable
      (integrable_deletionComponent G hG M hM j)
  have hsum := integrable_finsetSum Finset.univ
    (fun j _ => (hd j j.val).add (hd j (j.val + 1)))
  have hbound := integral_mono hleft hsum (abs_payoff_sub_le_hybrid_deletions M hM)
  have he : (∫ vw, ∑ j : Fin m,
      (deletionComponent M j (hybrid (firstCoordinates j.val) vw) +
        deletionComponent M j (hybrid (firstCoordinates (j.val + 1)) vw))
        ∂((vecLaw G).prod (vecLaw G))) = 2 * totalDeletionLoss (vecLaw G) M := by
    have hi := integral_finsetSum Finset.univ
      (fun j _ => (hd j j.val).add (hd j (j.val + 1)))
    simp only [Pi.add_apply] at hi
    rw [hi]
    simp_rw [integral_add (hd _ _) (hd _ _)]
    simp_rw [integral_hybrid G _ _ (integrable_deletionComponent G hG M hM _).aestronglyMeasurable]
    unfold totalDeletionLoss deletionLoss deletionComponent
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Pi.add_apply, Pi.sub_apply] at hbound
  rw [he] at hbound
  linarith

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma overlap_abs_identity (u v : ℝ) : u + v = 2 * min u v + |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv, abs_of_nonpos (sub_nonpos.mpr huv)]; ring
  · rw [min_eq_right hvu, abs_of_nonneg (sub_nonneg.mpr hvu)]; ring

lemma utility_decomposition {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M) :
    utility (vecLaw G) M ≤ totalDeletionLoss (vecLaw G) M +
      ∫ vw, min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ∂((vecLaw G).prod (vecLaw G)) := by
  have hu := integrable_payoff G hG M hM
  have hf := hu.comp_fst (vecLaw G)
  have hs := hu.comp_snd (vecLaw G)
  have hmin := hf.inf hs
  have habs := (hf.sub hs).abs
  have he : (∫ vw, buyerPayoff M vw.1 + buyerPayoff M vw.2 ∂((vecLaw G).prod (vecLaw G))) =
      2 * (∫ vw, min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ∂((vecLaw G).prod (vecLaw G))) +
        ∫ vw, |buyerPayoff M vw.1 - buyerPayoff M vw.2| ∂((vecLaw G).prod (vecLaw G)) := by
    have hpoint : (fun vw : (Fin m → ℝ≥0) × (Fin m → ℝ≥0) =>
        buyerPayoff M vw.1 + buyerPayoff M vw.2) =
      (fun vw => 2 * min (buyerPayoff M vw.1) (buyerPayoff M vw.2) +
        |buyerPayoff M vw.1 - buyerPayoff M vw.2|) := by
      funext vw
      exact overlap_abs_identity _ _
    rw [hpoint]
    have hi := integral_add (hmin.const_mul 2) habs
    simp only [Pi.add_apply, Pi.inf_apply, Pi.sub_apply] at hi
    rw [hi, integral_const_mul]
  rw [integral_add hf hs, integral_fun_fst, integral_fun_snd] at he
  simp only [probReal_univ, one_smul] at he
  have hd := eq_3_3 hm G hG M hM
  unfold utility
  linarith

lemma utility_le_deletion_add_lottery {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j))
    (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (ell : Fin m → ℝ) (hell : ∀ j, 0 < ell j ∧ ell j ≤ 1) :
    utility (vecLaw G) M ≤ totalDeletionLoss (vecLaw G) M +
      (∫ v, (⨆ j, ell j * (v j : ℝ)) ∂vecLaw G) *
        ∑ j, qAlloc (vecLaw G) M j / ell j := by
  exact (utility_decomposition hm G hG M hM).trans
    (add_le_add le_rfl (lemma_1 hm G hG M hM _ (fun _ => le_rfl) ell hell))

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma lotteryProb_positive {m : ℕ} (lam : Fin m → ℝ) (b : ℝ) (hb : 0 < b) (j : Fin m) :
    0 < lotteryProb lam b j := by
  unfold lotteryProb
  split_ifs with h
  · exact lt_min (by norm_num) (div_pos hb h)
  · norm_num

lemma lotteryProb_reciprocal {m : ℕ} (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (b : ℝ) (hb : 0 < b) (j : Fin m) : 1 / lotteryProb lam b j ≤ 1 + lam j / b := by
  unfold lotteryProb
  split_ifs with h
  · by_cases hr : b / lam j ≤ 1
    · rw [min_eq_right hr, one_div_div]
      linarith
    · rw [min_eq_left (le_of_not_ge hr)]
      have hq : 0 ≤ lam j / b := div_nonneg (hlam j) hb.le
      simpa only [div_one] using (show (1 : ℝ) ≤ 1 + lam j / b by linarith)
  · have hq : 0 ≤ lam j / b := div_nonneg (hlam j) hb.le
    simpa only [div_one] using (show (1 : ℝ) ≤ 1 + lam j / b by linarith)

lemma freeLottery_payoff_max {m : ℕ} (hm : 1 ≤ m) (ell : Fin m → ℝ)
    (hell : ∀ j, 0 ≤ ell j ∧ ell j ≤ 1) (v : Fin m → ℝ≥0) :
    buyerPayoff (freeLotteryMech ell).reduced v = ⨆ j, ell j * (v j : ℝ) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  unfold buyerPayoff
  simp only [SBRand.reduced, OGDProof.freeLottery_pay_zero, sub_zero, OGDProof.freeLottery_alloc]
  calc
    _ = ∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn
        (lotCandidates v (fun j => clamp01 (ell j)))) (some j)).toReal *
          (clamp01 (ell j) * (v j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = Utility7.SurplusProof.maximum (fun j (_ : Unit) => clamp01 (ell j) * (v j : ℝ)) () :=
      Utility7.ContentionProof.lottery_truthful_value ell v
    _ = _ := by
      simp only [Utility7.SurplusProof.maximum, OGDProof.clamp01_eq _ (hell _).1 (hell _).2]
      exact Finset.sup'_univ_eq_ciSup _

lemma freeLottery_utility_max {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (ell : Fin m → ℝ) (hell : ∀ j, 0 ≤ ell j ∧ ell j ≤ 1) :
    utility (vecLaw G) (freeLotteryMech ell).reduced =
      ∫ v, (⨆ j, ell j * (v j : ℝ)) ∂vecLaw G := by
  unfold utility
  simp_rw [freeLottery_payoff_max hm ell hell]

lemma qAlloc_unitDemand_sum {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) (hUD : IsUnitDemand C) :
    (∑ j, qAlloc (vecLaw G) C j) ≤ 1 := by
  have hs := integral_mono (integrable_finsetSum Finset.univ
    (fun j _ => integrable_allocation G C hC j)) (integrable_const (1 : ℝ)) hUD
  rw [integral_finsetSum _ (fun j _ => integrable_allocation G C hC j)] at hs
  simpa only [qAlloc, integral_const, probReal_univ, one_smul] using hs

lemma lottery_weighted_caps {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C) (hUD : IsUnitDemand C)
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j) (b : ℝ) (hb : 0 < b) :
    (∑ j, qAlloc (vecLaw G) C j / lotteryProb lam b j) ≤
      1 + (∑ j, lam j * qAlloc (vecLaw G) C j) / b := by
  calc
    _ ≤ ∑ j, (qAlloc (vecLaw G) C j + lam j * qAlloc (vecLaw G) C j / b) := by
      apply Finset.sum_le_sum
      intro j _
      have hq : 0 ≤ qAlloc (vecLaw G) C j := integral_nonneg (fun v => (hC.1 v j).1)
      have h := mul_le_mul_of_nonneg_left (lotteryProb_reciprocal lam hlam b hb j) hq
      convert h using 1 <;> ring
    _ = (∑ j, qAlloc (vecLaw G) C j) + (∑ j, lam j * qAlloc (vecLaw G) C j) / b := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ _ := add_le_add (qAlloc_unitDemand_sum G C hC hUD) le_rfl

theorem freeLottery_benchmark {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C)
    (hUD : IsUnitDemand C) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (b gamma : ℝ) (hb : 0 < b)
    (hlo : 2 * b - 2 * gamma ≤ utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced)
    (hhi : utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced ≤ 2 * b) :
    (utility (vecLaw G) C - totalDeletionLoss (vecLaw G) C) / 2 -
      (∑ j, lam j * qAlloc (vecLaw G) C j) - gamma ≤
      utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced -
        ∑ j, lam j * qAlloc (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced j := by
  let U := utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced
  let cost := ∑ j, lam j * qAlloc (vecLaw G) C j
  have hu0 : 0 ≤ U := by
    rw [show U = utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced from rfl,
      freeLottery_utility_max hm G _ (OGDProof.lotteryProb_mem lam b hb.le)]
    apply integral_nonneg
    intro v
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact (mul_nonneg (lotteryProb_positive lam b hb ⟨0, hm⟩).le (v ⟨0, hm⟩).coe_nonneg).trans
      (Finite.le_ciSup (fun j => lotteryProb lam b j * (v j : ℝ)) ⟨0, hm⟩)
  have hc0 : 0 ≤ cost := Finset.sum_nonneg (fun j _ =>
    mul_nonneg (hlam j) (integral_nonneg (fun v => (hC.1 v j).1)))
  have hbase := utility_le_deletion_add_lottery hm G hG C hC (lotteryProb lam b)
    (fun j => ⟨lotteryProb_positive lam b hb j, (OGDProof.lotteryProb_mem lam b hb.le j).2⟩)
  rw [← freeLottery_utility_max hm G _ (OGDProof.lotteryProb_mem lam b hb.le)] at hbase
  have hweight := mul_le_mul_of_nonneg_left (lottery_weighted_caps G C hC hUD lam hlam b hb) hu0
  have hratio : U / b ≤ 2 := (div_le_iff₀ hb).mpr hhi
  have hUC : utility (vecLaw G) C - totalDeletionLoss (vecLaw G) C ≤ U + 2 * cost := by
    calc
      _ ≤ U * (1 + cost / b) := by linarith only [hbase, hweight]
      _ = U + (U / b) * cost := by ring
      _ ≤ U + 2 * cost := add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio hc0)
  have hfree := OGDProof.freeLottery_lagrangian_ge_half (vecLaw G) lam hlam b gamma hb.le hlo
  linarith

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof
open Utility7.ContentionProof

noncomputable def priceWeight : ℝ := Real.exp 1 / (3 * Real.exp 1 - 2)

lemma priceWeight_bounds : 0 ≤ priceWeight ∧ priceWeight ≤ 1 := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  unfold priceWeight
  exact ⟨div_nonneg (Real.exp_pos _).le (by linarith),
    (div_le_one (by linarith)).mpr (by linarith)⟩

lemma coin_false_real (p : PMF Bool) : (p false).toReal = 1 - (p true).toReal := by
  have h := OGDProof.pmf_real_sum p
  rw [Fintype.sum_bool] at h
  linarith

lemma het_as_mixture {m : ℕ} (pr : Fin m → TwoPointPrice) (ell : Fin m → ℝ) :
    hetMech pr ell = mixture (coin priceWeight)
      (fun b : Bool => if b then postedPriceMech pr else freeLotteryMech ell) := by
  funext v
  unfold hetMech mixture priceWeight
  congr 1
  funext b
  cases b <;> rfl

lemma het_allocation {m : ℕ} (pr : Fin m → TwoPointPrice) (ell : Fin m → ℝ)
    (v : Fin m → ℝ≥0) (j : Fin m) :
    (hetMech pr ell).alloc v j = priceWeight * (postedPriceMech pr).alloc v j +
      (1 - priceWeight) * (freeLotteryMech ell).alloc v j := by
  rw [het_as_mixture]
  rw [mixture_allocation, tsum_fintype, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [coin_false_real, OGDProof.coin_true_toReal,
    OGDProof.clamp01_eq _ priceWeight_bounds.1 priceWeight_bounds.2]

lemma het_payoff {m : ℕ} (pr : Fin m → TwoPointPrice) (ell : Fin m → ℝ)
    (v : Fin m → ℝ≥0) : buyerPayoff (hetMech pr ell).reduced v =
      priceWeight * buyerPayoff (postedPriceMech pr).reduced v +
        (1 - priceWeight) * buyerPayoff (freeLotteryMech ell).reduced v := by
  have hGood (b : Bool) : Good (if b then postedPriceMech pr else freeLotteryMech ell) := by
    cases b
    · exact freeLottery_good ell
    · exact postedPrice_good pr
  have hh := mixture_reportUtility (coin priceWeight)
    (fun b : Bool => if b then postedPriceMech pr else freeLotteryMech ell)
    (fun b _ => (hGood b).2.1) (fun b _ => (hGood b).2.2) v v
  rw [tsum_fintype, Fintype.sum_bool] at hh
  simp only [Bool.false_eq_true, if_false, if_true] at hh
  rw [coin_false_real, OGDProof.coin_true_toReal,
    OGDProof.clamp01_eq _ priceWeight_bounds.1 priceWeight_bounds.2] at hh
  simpa only [← het_as_mixture, reportUtility, buyerPayoff, SBRand.reduced] using hh

lemma freeLottery_integrable_payoff {m : ℕ} (hm : 1 ≤ m)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (hG : ∀ j, IsValueLaw (G j)) (ell : Fin m → ℝ) :
    Integrable (buyerPayoff (freeLotteryMech ell).reduced) (vecLaw G) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hh := Utility7.SurplusProof.maximum_integrable
    (fun j (v : Fin m → ℝ≥0) => clamp01 (ell j) * (v j : ℝ))
    (fun j => by fun_prop) (fun j => (integrable_value G hG j).const_mul _)
    (fun j v => mul_nonneg (OGDProof.clamp01_mem _).1 (v j).coe_nonneg)
  have he : buyerPayoff (freeLotteryMech ell).reduced =
      Utility7.SurplusProof.maximum (fun j (v : Fin m → ℝ≥0) => clamp01 (ell j) * (v j : ℝ)) := by
    funext v
    unfold buyerPayoff
    simp only [SBRand.reduced, OGDProof.freeLottery_pay_zero, sub_zero, OGDProof.freeLottery_alloc]
    calc
      _ = ∑ j, ((ConsumerUtilityApprox.UnitDemand.uniformOn
        (lotCandidates v (fun j => clamp01 (ell j)))) (some j)).toReal *
          (clamp01 (ell j) * (v j : ℝ)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := lottery_truthful_value ell v
  rw [he]
  exact hh

lemma het_utility {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (pr : Fin m → TwoPointPrice) (ell : Fin m → ℝ) :
    utility (vecLaw G) (hetMech pr ell).reduced =
      priceWeight * utility (vecLaw G) (postedPriceMech pr).reduced +
        (1 - priceWeight) * utility (vecLaw G) (freeLotteryMech ell).reduced := by
  unfold utility
  simp_rw [het_payoff]
  rw [integral_add ((Utility7.PricingProof.postedPrice_integrable_payoff hm G hG pr).const_mul _)
    ((freeLottery_integrable_payoff hm G hG ell).const_mul _), integral_const_mul, integral_const_mul]

lemma het_qAlloc {m : ℕ} (pr : Fin m → TwoPointPrice) (ell : Fin m → ℝ)
    (G : Fin m → ProbabilityMeasure ℝ≥0) (j : Fin m) :
    qAlloc (vecLaw G) (hetMech pr ell).reduced j =
      priceWeight * qAlloc (vecLaw G) (postedPriceMech pr).reduced j +
        (1 - priceWeight) * qAlloc (vecLaw G) (freeLotteryMech ell).reduced j := by
  change (∫ v, (hetMech pr ell).alloc v j ∂vecLaw G) = _
  simp_rw [het_allocation]
  rw [integral_add ((Utility7.PricingProof.postedPrice_integrable_allocation pr (vecLaw G) j).const_mul _)
    ((OGDProof.freeLottery_alloc_integrable (vecLaw G) ell j).const_mul _),
      integral_const_mul, integral_const_mul]
  rfl

end Utility7.BenchmarkProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

lemma combine_branch_bounds (P F U D c delta gamma : ℝ)
    (hd : 0 ≤ delta) (hg : 0 ≤ gamma)
    (hP : (1 - Real.exp (-1)) * D - c - (1 - Real.exp (-1)) * delta ≤ P)
    (hF : (U - D) / 2 - c - gamma ≤ F) :
    U / (2 + Real.exp 1 / (Real.exp 1 - 1)) - c - delta - gamma ≤
      priceWeight * P + (1 - priceWeight) * F := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hn : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have he0 : Real.exp 1 ≠ 0 := (Real.exp_pos _).ne'
  have he1 : Real.exp 1 - 1 ≠ 0 := by linarith
  have he3 : 3 * Real.exp 1 - 2 ≠ 0 := by linarith
  have he3n : -2 + Real.exp 1 * 3 ≠ 0 := by linarith
  have heden : 2 + Real.exp 1 / (Real.exp 1 - 1) ≠ 0 := by
    exact ne_of_gt (add_pos (by norm_num) (div_pos (Real.exp_pos _) (by linarith)))
  have hp : priceWeight * (1 - Real.exp (-1)) = 1 / (2 + Real.exp 1 / (Real.exp 1 - 1)) := by
    unfold priceWeight
    rw [hn]
    field_simp [he0, he1, he3, heden]
    <;> ring
  have hf : (1 - priceWeight) / 2 = 1 / (2 + Real.exp 1 / (Real.exp 1 - 1)) := by
    rw [← hp]
    unfold priceWeight
    rw [hn]
    field_simp [he0, he3]
    <;> ring_nf
    <;> field_simp [he3n]
    <;> ring
  have ha : 0 ≤ 1 - Real.exp (-1) ∧ 1 - Real.exp (-1) ≤ 1 := by
    have hh := Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
    have h0 := Real.exp_pos (-1)
    constructor <;> linarith
  have hw := priceWeight_bounds
  have hpa : priceWeight * (1 - Real.exp (-1)) ≤ 1 := by nlinarith
  have hpd := mul_le_mul_of_nonneg_right hpa hd
  have hfg := mul_le_mul_of_nonneg_right (sub_le_self 1 hw.1) hg
  have hhP := mul_le_mul_of_nonneg_left hP hw.1
  have hhF := mul_le_mul_of_nonneg_left hF (sub_nonneg.mpr hw.2)
  have heq : priceWeight * ((1 - Real.exp (-1)) * D - c - (1 - Real.exp (-1)) * delta) +
      (1 - priceWeight) * ((U - D) / 2 - c - gamma) =
      U / (2 + Real.exp 1 / (Real.exp 1 - 1)) - c -
        priceWeight * (1 - Real.exp (-1)) * delta - (1 - priceWeight) * gamma := by
    have hdcoef : priceWeight * (1 - Real.exp (-1)) = (1 - priceWeight) / 2 := hp.trans hf.symm
    have hD := congrArg (fun x : ℝ => x * D) hdcoef
    have hU := congrArg (fun x : ℝ => x * U) hf
    linear_combination hD + hU
  linarith

lemma het_lagrangian {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (pr : Fin m → TwoPointPrice) (ell lam : Fin m → ℝ) :
    utility (vecLaw G) (hetMech pr ell).reduced -
      (∑ j, lam j * qAlloc (vecLaw G) (hetMech pr ell).reduced j) =
      priceWeight * (utility (vecLaw G) (postedPriceMech pr).reduced -
        ∑ j, lam j * qAlloc (vecLaw G) (postedPriceMech pr).reduced j) +
      (1 - priceWeight) * (utility (vecLaw G) (freeLotteryMech ell).reduced -
        ∑ j, lam j * qAlloc (vecLaw G) (freeLotteryMech ell).reduced j) := by
  rw [het_utility hm G hG]
  simp_rw [het_qAlloc]
  have hc : (∑ j, lam j * (priceWeight * qAlloc (vecLaw G) (postedPriceMech pr).reduced j +
      (1 - priceWeight) * qAlloc (vecLaw G) (freeLotteryMech ell).reduced j)) =
      priceWeight * (∑ j, lam j * qAlloc (vecLaw G) (postedPriceMech pr).reduced j) +
      (1 - priceWeight) * (∑ j, lam j * qAlloc (vecLaw G) (freeLotteryMech ell).reduced j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc]
  ring

theorem het_benchmark {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (C : Mechanism (Fin m)) (hC : IsTruthfulIRNPT C)
    (hUD : IsUnitDemand C) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (caps : Fin m → ℝ) (hcaps : IsFeasibleCaps caps) (delta gamma : ℝ)
    (hd : 0 ≤ delta) (hg : 0 ≤ gamma)
    (hopt : capOpt G lam - delta ≤ capObjective G lam caps)
    (pr : Fin m → TwoPointPrice) (hpr : ∀ j, IsImplementing (G j) (caps j) (pr j))
    (b : ℝ) (hb : 0 < b)
    (hlo : 2 * b - 2 * gamma ≤ utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced)
    (hhi : utility (vecLaw G) (freeLotteryMech (lotteryProb lam b)).reduced ≤ 2 * b) :
    utility (vecLaw G) C / (2 + Real.exp 1 / (Real.exp 1 - 1)) -
      (∑ j, lam j * qAlloc (vecLaw G) C j) - delta - gamma ≤
      utility (vecLaw G) (hetMech pr (lotteryProb lam b)).reduced -
        ∑ j, lam j * qAlloc (vecLaw G) (hetMech pr (lotteryProb lam b)).reduced j := by
  rw [het_lagrangian hm G hG]
  exact combine_branch_bounds _ _ _ _ _ _ _ hd hg
    (Utility7.PricingProof.pricing_benchmark hm G hG lam hlam caps hcaps delta hopt pr hpr C hC hUD)
    (freeLottery_benchmark hm G hG C hC hUD lam hlam b gamma hb hlo hhi)

end Utility7.BenchmarkProof


set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

noncomputable def interimMechanism {n m : ℕ} (I : Instance n m) (C : RMech n m) (i : Fin n) :
    Mechanism (Fin m) where
  q := C.interimAlloc I i
  s := C.interimPay I i

lemma reduced_allocation_bounds {n m : ℕ} (C : RMech n m) (hC : C.IsFeasible)
    (v : Profile n m) (i : Fin n) (j : Fin m) : 0 ≤ C.x v i j ∧ C.x v i j ≤ 1 := by
  refine ⟨(hC v).1 i j,?_⟩
  have hs : C.x v i j ≤ ∑k,C.x v i k :=
    Finset.single_le_sum (fun k _ => (hC v).1 i k) (Finset.mem_univ j)
  exact hs.trans ((hC v).2.1 i)

lemma measurable_interim_alloc {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsWellDefined I) (i : Fin n) (j : Fin m) : Measurable (fun w => C.interimAlloc I i w j) := by
  have h : Measurable (fun wv : (Fin m → ℝ≥0)×Profile n m =>
      C.x (Function.update wv.2 i wv.1) i j) := (hC.1 i j).comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_interim_pay {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsWellDefined I) (i : Fin n) : Measurable (C.interimPay I i) := by
  have h : Measurable (fun wv : (Fin m → ℝ≥0)×Profile n m =>
      C.p (Function.update wv.2 i wv.1) i) := (hC.2.1 i).comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_updated_alloc {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) (w : Fin m → ℝ≥0) (j : Fin m) :
    Integrable (fun v => C.x (Function.update v i w) i j) I.profileLaw := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((hC.1.1 i j).comp (by fun_prop)).aestronglyMeasurable
  filter_upwards [] with v
  have hb := reduced_allocation_bounds C hC.2.1 (Function.update v i w) i j
  change ‖C.x (Function.update v i w) i j‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

lemma interim_allocation_bounds {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) (w : Fin m → ℝ≥0) (j : Fin m) :
    0 ≤ C.interimAlloc I i w j ∧ C.interimAlloc I i w j ≤ 1 := by
  constructor
  · exact integral_nonneg (fun v => (reduced_allocation_bounds C hC.2.1 _ i j).1)
  · have h := integral_mono (integrable_updated_alloc I C hC i w j)
      (integrable_const (1 : ℝ)) (fun v => (reduced_allocation_bounds C hC.2.1 _ i j).2)
    simpa [RMech.interimAlloc] using h

lemma interim_unitDemand {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) : IsUnitDemand (interimMechanism I C i) := by
  intro w
  have hsum := integrable_finsetSum Finset.univ (fun j _ => integrable_updated_alloc I C hC i w j)
  change (∑j,∫v,C.x (Function.update v i w) i j ∂I.profileLaw) ≤ 1
  rw [←integral_finsetSum Finset.univ (fun j _ => integrable_updated_alloc I C hC i w j)]
  have h := integral_mono hsum (integrable_const (1 : ℝ))
    (fun v => (hC.2.1 (Function.update v i w)).2.1 i)
  simpa using h

lemma interim_buyerPayoff {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (i : Fin n) (v : Fin m → ℝ≥0) :
    buyerPayoff (interimMechanism I C i) v=C.interimUtil I i v v := by
  unfold buyerPayoff interimMechanism RMech.interimUtil
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

lemma interim_truthfulIRNPT {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) : IsTruthfulIRNPT (interimMechanism I C i) := by
  refine ⟨interim_allocation_bounds I C hC i,?_,?_,?_,?_,?_⟩
  · intro v w
    rw [interim_buyerPayoff]
    have h := hC.2.2.1 i v w
    simpa only [RMech.interimUtil,interimMechanism,mul_comm] using h
  · intro v
    rw [interim_buyerPayoff]
    exact hC.2.2.2.1 i v
  · intro w
    exact integral_nonneg (fun v => hC.2.2.2.2 (Function.update v i w) i)
  · exact measurable_interim_alloc I C hC.1 i
  · exact measurable_interim_pay I C hC.1 i

lemma interim_utility_sum {n m : ℕ} (I : Instance n m) (C : RMech n m) :
    C.U I=∑i,utility (I.buyerLaw i) (interimMechanism I C i) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply integral_congr_ae
  filter_upwards [] with v
  exact (interim_buyerPayoff I C i v).symm

end Utility7.BenchmarkProof


set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

noncomputable def profileHybrid {n m : ℕ} (s : Finset (Fin n))
    (vw : Profile n m×Profile n m) (i : Fin n) : Fin m → ℝ≥0 :=
  if i∈s then vw.1 i else vw.2 i

lemma measurePreserving_profileHybrid {n m : ℕ} (I : Instance n m) (s : Finset (Fin n)) :
    MeasurePreserving (profileHybrid (m := m) s) (I.profileLaw.prod I.profileLaw) I.profileLaw := by
  classical
  let ν := fun i => I.buyerLaw i
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin m → ℝ≥0) (Fin m → ℝ≥0) (Fin n)
  have he : MeasurePreserving e (Measure.pi (fun i => (ν i).prod (ν i)))
      ((Measure.pi ν).prod (Measure.pi ν)) :=
    measurePreserving_arrowProdEquivProdArrow (Fin m → ℝ≥0) (Fin m → ℝ≥0) (Fin n) ν ν
  have hp : MeasurePreserving (fun z : Fin n → (Fin m → ℝ≥0)×(Fin m → ℝ≥0) =>
      fun i => if i∈s then (z i).1 else (z i).2)
      (Measure.pi (fun i => (ν i).prod (ν i))) (Measure.pi ν) := by
    apply measurePreserving_pi (fun i => (ν i).prod (ν i)) ν
      (f := fun i z => if i∈s then z.1 else z.2)
    intro i
    by_cases hi : i∈s
    · simpa only [if_pos hi] using (measurePreserving_fst (μ := ν i) (ν := ν i))
    · simpa only [if_neg hi] using (measurePreserving_snd (μ := ν i) (ν := ν i))
  exact hp.comp (MeasurePreserving.symm e he)

lemma profileHybrid_singleton {n m : ℕ} (vw : Profile n m×Profile n m) (i : Fin n) :
    profileHybrid {i} vw=Function.update vw.2 i (vw.1 i) := by
  classical
  funext k
  by_cases hk : k=i
  · subst k
    simp [profileHybrid]
  · simp [profileHybrid,hk,Function.update_of_ne hk]

lemma measurable_profile_update_integral {n m : ℕ} (I : Instance n m) (i : Fin n)
    (f : Profile n m → ℝ) (hf : Measurable f) :
    Measurable (fun w : Fin m → ℝ≥0 => ∫v,f (Function.update v i w) ∂I.profileLaw) := by
  have h : Measurable (fun wv : (Fin m → ℝ≥0)×Profile n m => f (Function.update wv.2 i wv.1)) :=
    hf.comp (by fun_prop)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

lemma integral_profile_update {n m : ℕ} (I : Instance n m) (i : Fin n)
    (f : Profile n m → ℝ) (hf : Measurable f) (hfi : Integrable f I.profileLaw) :
    (∫w,∫v,f (Function.update v i w) ∂I.profileLaw ∂I.buyerLaw i)=∫v,f v ∂I.profileLaw := by
  have hprod : Integrable (fun vw : Profile n m×Profile n m =>
      f (Function.update vw.2 i (vw.1 i))) (I.profileLaw.prod I.profileLaw) := by
    simpa only [Function.comp_def,profileHybrid_singleton] using
      (measurePreserving_profileHybrid I {i}).integrable_comp_of_integrable hfi
  calc
    _ = ∫u,∫v,f (Function.update v i (u i)) ∂I.profileLaw ∂I.profileLaw :=
      (integral_comp_eval (μ := fun k => I.buyerLaw k) (i := i)
        (measurable_profile_update_integral I i f hf).aestronglyMeasurable).symm
    _ = ∫vw,f (Function.update vw.2 i (vw.1 i)) ∂I.profileLaw.prod I.profileLaw :=
      (integral_prod _ hprod).symm
    _ = ∫vw,f (profileHybrid {i} vw) ∂I.profileLaw.prod I.profileLaw := by
      simp_rw [profileHybrid_singleton]
    _ = _ := by
      have h := measurePreserving_profileHybrid I {i}
      have hi := integral_map h.measurable.aemeasurable (h.map_eq ▸ hfi.aestronglyMeasurable)
      rw [h.map_eq] at hi
      exact hi.symm

lemma integrable_reduced_alloc {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) (j : Fin m) :
    Integrable (fun v => C.x v i j) I.profileLaw := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) (hC.1.1 i j).aestronglyMeasurable
  filter_upwards [] with v
  change ‖C.x v i j‖ ≤ 1
  have hb := reduced_allocation_bounds C hC.2.1 v i j
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

lemma exAnteAlloc_eq_interim_qAlloc {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) (j : Fin m) :
    C.exAnteAlloc I i j=qAlloc (I.buyerLaw i) (interimMechanism I C i) j := by
  exact (integral_profile_update I i (fun v => C.x v i j) (hC.1.1 i j)
    (integrable_reduced_alloc I C hC i j)).symm

lemma integrable_interim_payoff {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) :
    Integrable (buyerPayoff (interimMechanism I C i)) (I.buyerLaw i) :=
  integrable_payoff (I.F i) (I.valueLaw i) _ (interim_truthfulIRNPT I C hC i)

lemma interim_payment_bounds {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) (w : Fin m → ℝ≥0) :
    0 ≤ C.interimPay I i w ∧ C.interimPay I i w ≤ ∑j,(w j : ℝ) := by
  have hm := interim_truthfulIRNPT I C hC i
  refine ⟨hm.2.2.2.1 w,?_⟩
  have hir := hm.2.2.1 w
  have hs : (∑j,(interimMechanism I C i).q w j*(w j : ℝ)) ≤ ∑j,(w j : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_of_le_one_left (w j).coe_nonneg (hm.1 w j).2
  unfold buyerPayoff at hir
  dsimp only [interimMechanism] at hir hs
  linarith

lemma integrable_interim_payment {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (i : Fin n) : Integrable (C.interimPay I i) (I.buyerLaw i) := by
  apply Integrable.mono' (integrable_finsetSum Finset.univ (fun j _ => integrable_value (I.F i) (I.valueLaw i) j))
    (measurable_interim_pay I C hC.1 i).aestronglyMeasurable
  filter_upwards [] with w
  have hb := interim_payment_bounds I C hC i w
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
  exact hb.2

lemma benchmark_exAnteFeasible {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) : C.IsExAnteFeasible I := by
  intro j
  change (∑i,∫v,C.x v i j ∂I.profileLaw) ≤ 1
  rw [←integral_finsetSum Finset.univ (fun i _ => integrable_reduced_alloc I C hC i j)]
  have h := integral_mono (integrable_finsetSum Finset.univ
    (fun i _ => integrable_reduced_alloc I C hC i j)) (integrable_const (1 : ℝ))
      (fun v => (hC.2.1 v).2.2 j)
  simpa using h

lemma interim_family_supply_feasible {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (j : Fin m) :
    (∑i,qAlloc (I.buyerLaw i) (interimMechanism I C i) j) ≤ 1 := by
  have h := benchmark_exAnteFeasible I C hC j
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  exact (exAnteAlloc_eq_interim_qAlloc I C hC i j).symm

end Utility7.BenchmarkProof


set_option autoImplicit false

open MeasureTheory
open scoped BigOperators
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.BenchmarkProof

theorem interim_benchmark_package {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) :
    (∀i,IsTruthfulIRNPT (interimMechanism I C i) ∧ IsUnitDemand (interimMechanism I C i)) ∧
      C.U I=∑i,utility (I.buyerLaw i) (interimMechanism I C i) ∧
      (∀i j,C.exAnteAlloc I i j=qAlloc (I.buyerLaw i) (interimMechanism I C i) j) ∧
      (∀i,Integrable (buyerPayoff (interimMechanism I C i)) (I.buyerLaw i) ∧
        Integrable (C.interimPay I i) (I.buyerLaw i)) := by
  exact ⟨fun i => ⟨interim_truthfulIRNPT I C hC i,interim_unitDemand I C hC i⟩,
    interim_utility_sum I C,exAnteAlloc_eq_interim_qAlloc I C hC,
    fun i => ⟨integrable_interim_payoff I C hC i,integrable_interim_payment I C hC i⟩⟩

end Utility7.BenchmarkProof


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace ConsumerUtilityApprox.UnitDemand.OGDProof
open Finset MeasureTheory ProbabilityTheory
open MultiItemRev.BundlingOpt
open scoped NNReal ENNReal

def zeroRMech (n m : ℕ) : RMech n m where
  x:=fun _ _ _=>0
  p:=fun _ _=>0

lemma zeroRMech_benchmark {n m : ℕ} (I : Instance n m) :
    (zeroRMech n m).IsBenchmarkClass I := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · refine ⟨fun i j=>measurable_const,fun i=>measurable_const,?_⟩
    intro i w
    exact integrable_zero _ _ _
  · intro v
    simp only [zeroRMech,zero_le,Finset.sum_const_zero]
    exact ⟨fun i j=>le_rfl,fun i=>by norm_num,fun j=>by norm_num⟩
  · intro i v w
    simp only [RMech.interimUtil,RMech.interimAlloc,RMech.interimPay,zeroRMech,
      integral_zero,mul_zero,Finset.sum_const_zero,sub_zero,le_refl]
  · intro i v
    simp only [RMech.interimUtil,RMech.interimAlloc,RMech.interimPay,zeroRMech,
      integral_zero,mul_zero,Finset.sum_const_zero,sub_zero,le_refl]
  · intro v i
    exact le_rfl

lemma zeroRMech_U {n m : ℕ} (I : Instance n m) : (zeroRMech n m).U I=0 := by
  simp only [RMech.U,RMech.interimUtil,RMech.interimAlloc,RMech.interimPay,zeroRMech,
    integral_zero,mul_zero,Finset.sum_const_zero,sub_zero]

lemma benchmark_nonempty {n m : ℕ} (I : Instance n m) :
    {u:ℝ|∃M:RMech n m,M.IsBenchmarkClass I ∧ M.U I=u}.Nonempty :=
  ⟨0,zeroRMech n m,zeroRMech_benchmark I,zeroRMech_U I⟩

/-- Taking the benchmark supremum requires no optimizer or attainment
hypothesis. The zero mechanism supplies nonemptiness internally. -/
theorem OPT_div_le_of_comparison {n m : ℕ} (I : Instance n m) (C B : ℝ) (hC:0<C)
    (h:∀M:RMech n m,M.IsBenchmarkClass I→M.U I/C ≤ B) : OPT I/C ≤ B := by
  apply (div_le_iff₀ hC).mpr
  apply csSup_le (benchmark_nonempty I)
  intro u hu
  obtain ⟨M,hM,rfl⟩:=hu
  exact (div_le_iff₀ hC).mp (h M hM)

/-- Assembly checkpoint only: the roundwise utility guarantee is the
remaining mechanism-theoretic content of public Lemma12, not an axiom
or an imported Open result. -/
theorem utility_minus_excess_of_round_bound {n m T : ℕ} (hn:1 ≤ n) (hT:1 ≤ T)
    (I : Instance n m) (M : ℕ→Fin n→SBRand m) (lam : ℕ→Fin m→ℝ)
    (h0:∀j,lam 0 j=0)
    (hu:∀t<T,∀j,lam (t+1) j=min 1 (max 0 (lam t j+1/((n:ℝ)*Real.sqrt T)*
      ((∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1))))
    (K : ℝ)
    (hround:∀t<T,K ≤ (∑i,utility (I.buyerLaw i) (M t i).reduced)-
      ∑j,lam t j*((∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1)) :
    K-(n:ℝ)*m/Real.sqrt T  ≤ 
      (1/(T:ℝ))*(∑t∈range T,∑i,utility (I.buyerLaw i) (M t i).reduced)-
      ∑j,max ((1/(T:ℝ))*(∑t∈range T,∑i,qAlloc (I.buyerLaw i) (M t i).reduced j)-1) 0 := by
  have hTR:0<(T:ℝ) := by exact_mod_cast (show 0<T by omega)
  have hs:=sum_le_sum (fun t (ht:t∈range T)=>hround t (mem_range.mp ht))
  rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.sum_sub_distrib] at hs
  have ha:=mul_le_mul_of_nonneg_left hs (one_div_pos.mpr hTR).le
  rw [mul_sub] at ha
  have he:(1/(T:ℝ))*((T:ℝ)*K)=K := by field_simp
  rw [he] at ha
  have hg:=actual_excess_requests_bound hn hT I M lam h0 hu
  linarith

end ConsumerUtilityApprox.UnitDemand.OGDProof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.Lemma12Proof

noncomputable section
open Utility7.BenchmarkProof

lemma approximation_denominator_pos : 0 < 2 + Real.exp 1 / (Real.exp 1 - 1) := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hp : 0 < Real.exp 1 / (Real.exp 1 - 1) :=
    div_pos (Real.exp_pos _) (by linarith)
  linarith

lemma weighted_interim_supply {n m : ℕ} (I : Instance n m) (C : RMech n m)
    (hC : C.IsBenchmarkClass I) (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j) :
    (∑ i, ∑ j, lam j * qAlloc (I.buyerLaw i) (interimMechanism I C i) j) ≤
      ∑ j, lam j := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ j, lam j * (∑ i, qAlloc (I.buyerLaw i) (interimMechanism I C i) j) := by
      simp_rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun j _ =>
      mul_le_of_le_one_right (hlam j) (interim_family_supply_feasible I C hC j))

lemma excess_cost_identity {n m : ℕ} (I : Instance n m) (M : Fin n → SBRand m)
    (lam : Fin m → ℝ) :
    (∑ j, lam j * ((∑ i, qAlloc (I.buyerLaw i) (M i).reduced j) - 1)) =
      (∑ i, ∑ j, lam j * qAlloc (I.buyerLaw i) (M i).reduced j) - ∑ j, lam j := by
  simp_rw [mul_sub, mul_one, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]

end
end Utility7.Lemma12Proof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.Lemma12Proof

noncomputable section
open Utility7.BenchmarkProof

/-- Sum the genuine single-buyer bounds against the interim mechanisms of an
arbitrary admissible benchmark, using the benchmark's actual supply constraint. -/
theorem round_comparison {n m : ℕ} (hm : 1 ≤ m) (I : Instance n m)
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (caps : Fin n → Fin m → ℝ)
    (delta gamma : ℝ) (hd : 0 ≤ delta) (hg : 0 ≤ gamma)
    (hcaps : ∀ i, IsFeasibleCaps (caps i) ∧
      capOpt (I.F i) lam - delta ≤ capObjective (I.F i) lam (caps i))
    (pr : Fin n → Fin m → TwoPointPrice)
    (hpr : ∀ i j, IsImplementing (I.F i j) (caps i j) (pr i j))
    (b : Fin n → ℝ)
    (hb : ∀ i, 0 < b i ∧
      2 * b i - 2 * gamma ≤ utility (I.buyerLaw i)
        (freeLotteryMech (lotteryProb lam (b i))).reduced ∧
      utility (I.buyerLaw i) (freeLotteryMech (lotteryProb lam (b i))).reduced ≤ 2 * b i)
    (C : RMech n m) (hC : C.IsBenchmarkClass I) :
    C.U I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * (delta + gamma) ≤
      (∑ i, utility (I.buyerLaw i) (hetMech (pr i) (lotteryProb lam (b i))).reduced) -
        ∑ j, lam j * ((∑ i, qAlloc (I.buyerLaw i)
          (hetMech (pr i) (lotteryProb lam (b i))).reduced j) - 1) := by
  have hint := interim_benchmark_package I C hC
  have hi (i : Fin n) := het_benchmark hm (I.F i) (I.valueLaw i)
    (interimMechanism I C i) (hint.1 i).1 (hint.1 i).2 lam hlam
    (caps i) (hcaps i).1 delta gamma hd hg (hcaps i).2 (pr i) (hpr i)
    (b i) (hb i).1 (hb i).2.1 (hb i).2.2
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  change (∑ i, (utility (I.buyerLaw i) (interimMechanism I C i) /
      (2 + Real.exp 1 / (Real.exp 1 - 1)) -
        (∑ j, lam j * qAlloc (I.buyerLaw i) (interimMechanism I C i) j) - delta - gamma)) ≤
    ∑ i, (utility (I.buyerLaw i) (hetMech (pr i) (lotteryProb lam (b i))).reduced -
      ∑ j, lam j * qAlloc (I.buyerLaw i)
        (hetMech (pr i) (lotteryProb lam (b i))).reduced j) at hs
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  rw [← hint.2.1] at hs
  have hc := weighted_interim_supply I C hC lam hlam
  rw [excess_cost_identity]
  nlinarith only [hs, hc]

/-- The paper's roundwise (C.6), with the supremum taken over the full original
benchmark class. No attaining mechanism is assumed. -/
theorem round_opt_bound {n m : ℕ} (hm : 1 ≤ m) (I : Instance n m)
    (lam : Fin m → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (caps : Fin n → Fin m → ℝ)
    (delta gamma : ℝ) (hd : 0 ≤ delta) (hg : 0 ≤ gamma)
    (hcaps : ∀ i, IsFeasibleCaps (caps i) ∧
      capOpt (I.F i) lam - delta ≤ capObjective (I.F i) lam (caps i))
    (pr : Fin n → Fin m → TwoPointPrice)
    (hpr : ∀ i j, IsImplementing (I.F i j) (caps i j) (pr i j))
    (b : Fin n → ℝ)
    (hb : ∀ i, 0 < b i ∧
      2 * b i - 2 * gamma ≤ utility (I.buyerLaw i)
        (freeLotteryMech (lotteryProb lam (b i))).reduced ∧
      utility (I.buyerLaw i) (freeLotteryMech (lotteryProb lam (b i))).reduced ≤ 2 * b i) :
    OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * (delta + gamma) ≤
      (∑ i, utility (I.buyerLaw i) (hetMech (pr i) (lotteryProb lam (b i))).reduced) -
        ∑ j, lam j * ((∑ i, qAlloc (I.buyerLaw i)
          (hetMech (pr i) (lotteryProb lam (b i))).reduced j) - 1) := by
  have hsup := OGDProof.OPT_div_le_of_comparison I
    (2 + Real.exp 1 / (Real.exp 1 - 1))
    (((∑ i, utility (I.buyerLaw i) (hetMech (pr i) (lotteryProb lam (b i))).reduced) -
      ∑ j, lam j * ((∑ i, qAlloc (I.buyerLaw i)
        (hetMech (pr i) (lotteryProb lam (b i))).reduced j) - 1)) +
          (n : ℝ) * (delta + gamma)) approximation_denominator_pos (fun C hC => by
      have h := round_comparison hm I lam hlam caps delta gamma hd hg hcaps pr hpr b hb C hC
      linarith only [h])
  linarith only [hsup]

end
end Utility7.Lemma12Proof


open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand MultiItemRev.BundlingOpt

namespace Utility7.Lemma12Proof

theorem lemma_12 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (hnorm : ∑ i, ∑ j, mean (I.F i j) = 1)
    (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (T : ℕ) (hT : 1 ≤ T)
    (lam : ℕ → Fin m → ℝ) (caps : ℕ → Fin n → Fin m → ℝ)
    (pr : ℕ → Fin n → Fin m → TwoPointPrice) (b : ℕ → Fin n → ℝ)
    (hcaps : ∀ t < T, ∀ i, IsFeasibleCaps (caps t i) ∧
      capOpt (I.F i) (lam t) - δ ≤ capObjective (I.F i) (lam t) (caps t i))
    (hpr : ∀ t < T, ∀ i j, IsImplementing (I.F i j) (caps t i j) (pr t i j))
    (hb : ∀ t < T, ∀ i, 0 < b t i ∧
      2 * b t i - 2 * γ
        ≤ utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced ∧
      utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced
        ≤ 2 * b t i)
    (hlam0 : ∀ j, lam 0 j = 0)
    (hlam : ∀ t < T, ∀ j, lam (t + 1) j =
      min 1 (max 0 (lam t j + 1 / ((n : ℝ) * Real.sqrt T) *
        (∑ i, qAlloc (I.buyerLaw i)
          (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j - 1)))) :
    OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * m / Real.sqrt T - n * (δ + γ)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
          utility (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced
        - ∑ j, max ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
            qAlloc (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j
              - 1) 0 := by
  let M : ℕ → Fin n → SBRand m := fun t i =>
    hetMech (pr t i) (lotteryProb (lam t) (b t i))
  have hmem := OGDProof.lam_mem lam
    (fun t j => (∑ i, qAlloc (I.buyerLaw i) (M t i).reduced j) - 1)
    (1 / ((n : ℝ) * Real.sqrt T)) hlam0 hlam
  have hround (t : ℕ) (ht : t < T) :
      OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * (δ + γ) ≤
        (∑ i, utility (I.buyerLaw i) (M t i).reduced) -
          ∑ j, lam t j * ((∑ i, qAlloc (I.buyerLaw i) (M t i).reduced j) - 1) := by
    exact round_opt_bound hm I (lam t) (fun j => (hmem t (Nat.le_of_lt ht) j).1)
      (caps t) δ γ hδ0.le hγ0.le (hcaps t ht) (pr t) (hpr t ht) (b t) (hb t ht)
  have hfinal := OGDProof.utility_minus_excess_of_round_bound hn hT I M lam hlam0 hlam
    (OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * (δ + γ)) hround
  dsimp only [M] at hfinal
  linarith only [hfinal]

end Utility7.Lemma12Proof

open ConsumerUtilityApprox.UnitDemand
open ConsumerUtilityApprox.UnitDemand
open MultiItemRev.BundlingOpt
open MeasureTheory
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (hnorm : ∑ i, ∑ j, mean (I.F i j) = 1)
    (δ γ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (T : ℕ) (hT : 1 ≤ T)
    (lam : ℕ → Fin m → ℝ) (caps : ℕ → Fin n → Fin m → ℝ)
    (pr : ℕ → Fin n → Fin m → TwoPointPrice) (b : ℕ → Fin n → ℝ)
    (hcaps : ∀ t < T, ∀ i, IsFeasibleCaps (caps t i) ∧
      capOpt (I.F i) (lam t) - δ ≤ capObjective (I.F i) (lam t) (caps t i))
    (hpr : ∀ t < T, ∀ i j, IsImplementing (I.F i j) (caps t i j) (pr t i j))
    (hb : ∀ t < T, ∀ i, 0 < b t i ∧
      2 * b t i - 2 * γ
        ≤ utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced ∧
      utility (I.buyerLaw i) (freeLotteryMech (lotteryProb (lam t) (b t i))).reduced
        ≤ 2 * b t i)
    (hlam0 : ∀ j, lam 0 j = 0)
    (hlam : ∀ t < T, ∀ j, lam (t + 1) j =
      min 1 (max 0 (lam t j + 1 / ((n : ℝ) * Real.sqrt T) *
        (∑ i, qAlloc (I.buyerLaw i)
          (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j - 1)))) :
    OPT I / (2 + Real.exp 1 / (Real.exp 1 - 1)) - (n : ℝ) * m / Real.sqrt T - n * (δ + γ)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
          utility (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced
        - ∑ j, max ((1 / (T : ℝ)) * ∑ t ∈ Finset.range T, ∑ i,
            qAlloc (I.buyerLaw i) (hetMech (pr t i) (lotteryProb (lam t) (b t i))).reduced j
              - 1) 0  := by exact Utility7.Lemma12Proof.lemma_12 hn hm I hnorm δ γ hδ0 hδ1 hγ0 hγ1 T hT lam caps pr b hcaps hpr hb hlam0 hlam
