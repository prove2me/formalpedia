-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.eq_5_12
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:59:40.241101+00:00
-- url     : https://prove2.me/submissions/74b16528-80b2-4628-aad4-f302449e91cb

import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
import Mathlib
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model

-- Source module: Solutions.Utility7IndependentPMF
section

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
end

-- Source module: Solutions.Utility7IndependentMap
section

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
end

-- Source module: Solutions.Utility7PMFExpectation
section

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
end

-- Source module: Solutions.Utility7FairExponential
section

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
end

-- Source module: Solutions.Utility7IndependentSurplus
section

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
end

-- Source module: Solutions.Utility7PostedPointwise
section

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
end

-- Source module: Solutions.Utility7ContentionOutcomes
section

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
end

-- Source module: Solutions.Utility7PreLawMarginal
section

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
end

-- Source module: Solutions.Utility7RequestIndicators
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def requestsItem {m : ℕ} (j : Fin m) (r : Request m) : Bool :=
  decide (r.map Prod.fst = some j)

lemma request_probability {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (w : Fin m → ℝ≥0) (j : Fin m) :
    (((D.request i w).map (requestsItem j)) true).toReal = (requestMech D i).alloc w j := by
  unfold requestMech SBRand.alloc
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply, PMF.map_apply]
  congr 1
  apply tsum_congr
  intro r
  cases r with
  | none => simp [requestsItem, Request.toOutcome, Set.indicator]
  | some a =>
    obtain ⟨k, p⟩ := a
    simp [requestsItem, Request.toOutcome, Set.indicator]

lemma bool_false_probability (p : PMF Bool) : (p false).toReal = 1 - (p true).toReal := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype, Fintype.sum_bool,
    ENNReal.toReal_add (p.apply_ne_top true) (p.apply_ne_top false)] at h
  norm_num at h
  linarith

lemma requesters_distribution {n m : ℕ} (p : Fin n → PMF (Request m)) (j : Fin m) :
    (indep n p).map (fun req => MechDescription.requesters req j) =
      (indep n (fun i => (p i).map (requestsItem j))).map boolSet := by
  rw [← indep_map, PMF.map_comp]
  congr 1
  funext req
  ext k
  simp [MechDescription.requesters, boolSet, requestsItem]

lemma requesters_probability {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (j : Fin m) (A : Finset (Fin n)) :
    (((indep n (fun i => D.request i (v i))).map
      (fun req => MechDescription.requesters req j)) A).toReal =
      ∏ i, if i ∈ A then (requestMech D i).alloc (v i) j
        else 1 - (requestMech D i).alloc (v i) j := by
  rw [requesters_distribution, indep_boolSet_apply, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [if_pos hi, request_probability]
  · simp only [if_neg hi, bool_false_probability, request_probability]

lemma mean_requesters {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (j : Fin m) (G : Finset (Fin n) → ℝ) (hG : ∀ A, 0 ≤ G A) :
    (∑' req, (indep n (fun i => D.request i (v i)) req).toReal *
      G (MechDescription.requesters req j)) =
      ∑ A : Finset (Fin n),
        (∏ i, if i ∈ A then (requestMech D i).alloc (v i) j
          else 1 - (requestMech D i).alloc (v i) j) * G A := by
  rw [← mean_map _ (fun req => MechDescription.requesters req j) G
    (fun req _ => hG _), tsum_fintype]
  simp_rw [requesters_probability]

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7FairWeights
section

open scoped BigOperators

namespace Utility7.FairProof

noncomputable def weight {α : Type*} [DecidableEq α] (q : α → ℝ)
    (s A : Finset α) : ℝ := ∏ k ∈ s, if k ∈ A then q k else 1 - q k

variable {α : Type*} [DecidableEq α] (q : α → ℝ)

lemma weight_insert_absent {s A : Finset α} {k : α} (hk : k ∉ s)
    (hA : A ⊆ s) : weight q (insert k s) A = (1 - q k) * weight q s A := by
  have hkA : k ∉ A := fun h => hk (hA h)
  simp [weight, Finset.prod_insert, hk, hkA]

lemma weight_insert_present {s A : Finset α} {k : α} (hk : k ∉ s)
    (hA : A ⊆ s) : weight q (insert k s) (insert k A) = q k * weight q s A := by
  rw [weight, Finset.prod_insert hk]
  simp only [Finset.mem_insert_self, if_true]
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  have hxk : x ≠ k := fun h => hk (h ▸ hx)
  simp [hxk]

lemma sum_weight (s : Finset α) : ∑ A ∈ s.powerset, weight q s A = 1 := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert k s hk ih =>
    rw [Finset.sum_powerset_insert hk]
    calc
      _ = ∑ A ∈ s.powerset, ((1 - q k) * weight q s A + q k * weight q s A) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro A hA
        rw [weight_insert_absent q hk (Finset.mem_powerset.mp hA),
          weight_insert_present q hk (Finset.mem_powerset.mp hA)]
      _ = ∑ A ∈ s.powerset, weight q s A := by congr 1; funext A; ring
      _ = 1 := ih

/-- Insertion of a single independent Bernoulli request. -/
lemma coordinate_balance (s : Finset α) (k : α) (hk : k ∈ s) :
    (∑ A ∈ s.powerset, weight q s A *
      (if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1))) =
    ∑ A ∈ s.powerset, weight q s A * (if k ∈ A then 1 / (A.card : ℝ) else 0) := by
  let t := s.erase k
  have hkt : k ∉ t := Finset.notMem_erase _ _
  have hs : s = insert k t := (Finset.insert_erase hk).symm
  rw [hs, Finset.sum_powerset_insert hkt, Finset.sum_powerset_insert hkt]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  have hAt : A ⊆ t := Finset.mem_powerset.mp hA
  have hkA : k ∉ A := fun h => hkt (hAt h)
  rw [weight_insert_absent q hkt hAt, weight_insert_present q hkt hAt]
  simp only [hkA, if_false, Finset.mem_insert_self, if_true,
    Finset.card_insert_of_notMem hkA, Nat.cast_add, Nat.cast_one, mul_zero, add_zero]
  ring

lemma numerator_eq_sum (s A : Finset α) (hA : A ⊆ s) :
    (∑ k ∈ A, q k) / (A.card : ℝ) +
      (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1) =
    ∑ k ∈ s, if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1) := by
  rw [Finset.sum_ite]
  have hfilter : s.filter (fun k => k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hA h
  have hfilter' : s.filter (fun k => k ∉ A) = s \ A := by ext k; simp
  rw [hfilter, hfilter', Finset.sum_div, Finset.sum_div]

lemma sum_reciprocal (s A : Finset α) (hA : A ⊆ s) :
    (∑ k ∈ s, if k ∈ A then 1 / (A.card : ℝ) else 0) =
      if A = ∅ then 0 else 1 := by
  rw [Finset.sum_ite]
  have hfilter : s.filter (fun k => k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun h => hA h
  rw [hfilter]
  by_cases he : A = ∅
  · simp [he]
  · have hc : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he))
    simp [he, hc]

lemma sum_numerator (s : Finset α) :
    (∑ A ∈ s.powerset, weight q s A *
      ((∑ k ∈ A, q k) / (A.card : ℝ) +
        (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1))) =
      1 - weight q s ∅ := by
  calc
    _ = ∑ A ∈ s.powerset, weight q s A *
        ∑ k ∈ s, if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [numerator_eq_sum q s A (Finset.mem_powerset.mp hA)]
    _ = ∑ k ∈ s, ∑ A ∈ s.powerset, weight q s A *
        (if k ∈ A then q k / (A.card : ℝ) else q k / ((A.card : ℝ) + 1)) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ A ∈ s.powerset, weight q s A *
        (if k ∈ A then 1 / (A.card : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact coordinate_balance q s k hk
    _ = ∑ A ∈ s.powerset, weight q s A *
        (if A = ∅ then 0 else 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A hA
      rw [← Finset.mul_sum, sum_reciprocal s A (Finset.mem_powerset.mp hA)]
    _ = (∑ A ∈ s.powerset, weight q s A) - weight q s ∅ := by
      have he : ∅ ∈ s.powerset := by simp
      simp only [mul_ite, mul_zero, mul_one]
      have hh : (∑ A ∈ s.powerset, if A = ∅ then 0 else weight q s A) =
          ∑ A ∈ s.powerset.erase ∅, weight q s A := by
        rw [← Finset.sum_erase_add _ _ he]
        simp only [ite_true, add_zero]
        apply Finset.sum_congr rfl
        intro A hA
        simp [Finset.ne_of_mem_erase hA]
      rw [hh]
      have hh' := Finset.sum_erase_add s.powerset (weight q s) he
      linarith
    _ = 1 - weight q s ∅ := by rw [sum_weight]

end Utility7.FairProof
end

-- Source module: Solutions.Utility7FairSelection
section

open scoped BigOperators
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.FairProof

lemma scaled_fair {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m) (i : Fin n)
    (hS : ∑ k, Q k j ≠ 0) (A : Finset (Fin n)) (hA : A ⊆ Finset.univ.erase i) :
    (∑ k, Q k j) * fairSelProb Q j (insert i A) i =
      ((∑ k ∈ A, Q k j) / (A.card : ℝ) +
        (∑ k ∈ (Finset.univ.erase i) \ A, Q k j) / ((A.card : ℝ) + 1)) +
      if A = ∅ then Q i j else 0 := by
  have hiA : i ∉ A := fun hi => Finset.notMem_erase i Finset.univ (hA hi)
  by_cases he : A = ∅
  · subst A
    simp only [fairSelProb, Finset.insert_empty, Finset.mem_singleton, not_true_eq_false,
      if_false, Finset.card_singleton, if_true, mul_one, Finset.sum_empty, Finset.card_empty,
      Nat.cast_zero, zero_div, Finset.sdiff_empty, zero_add, div_one]
    exact (Finset.sum_erase_add Finset.univ (fun k => Q k j) (Finset.mem_univ i)).symm
  · have hcard : (insert i A).card ≠ 1 := by
      rw [Finset.card_insert_of_notMem hiA]
      have hnon := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      omega
    have herase : (insert i A).erase i = A := Finset.erase_insert hiA
    have hcard' : A.card + 1 ≠ 1 := by
      simpa only [Finset.card_insert_of_notMem hiA] using hcard
    have hdiff : Finset.univ \ insert i A = (Finset.univ.erase i) \ A := by
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase]
      tauto
    simp only [fairSelProb, Finset.mem_insert_self, not_true_eq_false, if_false, hcard,
      hS, herase, hdiff, Finset.card_insert_of_notMem hiA, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, he, add_zero, hcard']
    rw [← mul_assoc, mul_one_div_cancel hS, one_mul]

lemma fair_expectation_nonzero {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (i : Fin n) (hS : ∑ k, Q k j ≠ 0) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        weight (fun k => Q k j) (Finset.univ.erase i) A * fairSelProb Q j (insert i A) i) =
      selectionConst Q j := by
  let s : Finset (Fin n) := Finset.univ.erase i
  let q : Fin n → ℝ := fun k => Q k j
  have hnum := sum_numerator q s
  have hscaled : (∑ k, Q k j) *
      (∑ A ∈ s.powerset, weight q s A * fairSelProb Q j (insert i A) i) =
        (1 - weight q s ∅) + weight q s ∅ * Q i j := by
    calc
      _ = ∑ A ∈ s.powerset, weight q s A *
          ((∑ k, Q k j) * fairSelProb Q j (insert i A) i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        ring
      _ = ∑ A ∈ s.powerset, weight q s A *
          (((∑ k ∈ A, q k) / (A.card : ℝ) +
            (∑ k ∈ s \ A, q k) / ((A.card : ℝ) + 1)) +
          if A = ∅ then Q i j else 0) := by
        apply Finset.sum_congr rfl
        intro A hA
        rw [scaled_fair Q j i hS A (Finset.mem_powerset.mp hA)]
      _ = _ := by
        simp_rw [mul_add] at hnum ⊢
        rw [Finset.sum_add_distrib, hnum]
        simp
  have hprod : (∏ k, (1 - Q k j)) = (1 - Q i j) * weight q s ∅ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => 1 - Q k j) (Finset.mem_univ i)]
    rfl
  unfold selectionConst
  rw [if_neg hS]
  apply (eq_div_iff hS).mpr
  change (∑ A ∈ s.powerset, weight q s A * fairSelProb Q j (insert i A) i) *
      (∑ k, Q k j) = _
  rw [mul_comm, hscaled, hprod]
  ring

lemma fair_expectation_zero {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (i : Fin n) (hQ : ∀ k, 0 ≤ Q k j) (hS : ∑ k, Q k j = 0) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        weight (fun k => Q k j) (Finset.univ.erase i) A * fairSelProb Q j (insert i A) i) =
      selectionConst Q j := by
  have hz : ∀ k, Q k j = 0 := by
    intro k
    have h := Finset.single_le_sum (fun k _ => hQ k) (Finset.mem_univ k)
    rw [hS] at h
    exact le_antisymm h (hQ k)
  rw [selectionConst, if_pos hS]
  trans weight (fun k => Q k j) (Finset.univ.erase i) ∅ * fairSelProb Q j (insert i ∅) i
  · apply Finset.sum_eq_single ∅
    · intro A hA hne
      have hnon : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨k, hk⟩ := hnon
      have hks := (Finset.mem_powerset.mp hA) hk
      have hw : weight (fun k => Q k j) (Finset.univ.erase i) A = 0 := by
        apply Finset.prod_eq_zero hks
        simp [hk, hz k]
      simp [hw]
    · simp
  · simp [weight, fairSelProb, hz]

theorem eq_5_11 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (Q : Fin n → Fin m → ℝ)
    (hQ : ∀ k j, 0 ≤ Q k j ∧ Q k j ≤ 1) (hfeas : ∀ j, ∑ k, Q k j ≤ 1)
    (j : Fin m) (i : Fin n) :
    (∑ A ∈ (Finset.univ.erase i).powerset,
        (∏ k ∈ Finset.univ.erase i, if k ∈ A then Q k j else 1 - Q k j) *
          fairSelProb Q j (insert i A) i) = selectionConst Q j ∧
      1 - Real.exp (-1) ≤ selectionConst Q j := by
  constructor
  · by_cases hS : ∑ k, Q k j = 0
    · exact fair_expectation_zero Q j i (fun k => (hQ k j).1) hS
    · exact fair_expectation_nonzero Q j i hS
  · unfold selectionConst
    split_ifs with hS
    · linarith [Real.exp_pos (-1)]
    · have hnonneg : 0 ≤ ∑ k, Q k j := Finset.sum_nonneg (fun k _ => (hQ k j).1)
      exact selection_lower_bound Finset.univ (fun k => Q k j) (fun k _ => hQ k j)
        (hfeas j) (lt_of_le_of_ne hnonneg (Ne.symm hS))

end Utility7.FairProof
end

-- Source module: Solutions.Utility7FairDistribution
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.FairProof

lemma sum_erase_rows {n : ℕ} (q : Fin n → ℝ) (A : Finset (Fin n)) :
    (∑ i ∈ A, ∑ k ∈ A.erase i, q k) = ((A.card : ℝ) - 1) * ∑ k ∈ A, q k := by
  calc
    _ = ∑ i ∈ A, ((∑ k ∈ A, q k) - q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := Finset.sum_erase_add A q hi
      linarith
    _ = _ := by rw [Finset.sum_sub_distrib]; simp; ring

lemma fair_sum {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (A : Finset (Fin n)) (hA : A.Nonempty) : ∑ i, fairSelProb Q j A i = 1 := by
  have ha : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hA)
  have hrestrict : (∑ i, fairSelProb Q j A i) = ∑ i ∈ A, fairSelProb Q j A i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ A)
    intro i _ hi
    simp [fairSelProb, hi]
  rw [hrestrict]
  by_cases h1 : A.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    simp [fairSelProb]
  · by_cases hS : ∑ k, Q k j = 0
    · simp [fairSelProb, h1, hS, Finset.sum_ite_mem, ha]
    · have ha1 : (A.card : ℝ) - 1 ≠ 0 := by
        intro h
        have hc : A.card = 1 := by exact_mod_cast (by linarith : (A.card : ℝ) = 1)
        exact h1 hc
      have htotal : (∑ k ∈ A, Q k j) + ∑ k ∈ Finset.univ \ A, Q k j = ∑ k, Q k j :=
        Finset.sum_add_sum_compl A (fun k => Q k j)
      calc
        _ = (1 / ∑ k, Q k j) *
            ((∑ i ∈ A, ∑ k ∈ A.erase i, Q k j) / ((A.card : ℝ) - 1) +
              (A.card : ℝ) * (∑ k ∈ Finset.univ \ A, Q k j) / (A.card : ℝ)) := by
          simp only [fairSelProb, h1, hS, if_false]
          simp only [Finset.sum_ite, Finset.filter_notMem_eq_sdiff, Finset.sdiff_self,
            Finset.sum_empty, zero_add, not_not, Finset.filter_mem_eq_inter, Finset.inter_self]
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
            Finset.sum_const, nsmul_eq_mul]
          ring
        _ = 1 := by
          rw [sum_erase_rows]
          field_simp [ha, ha1, hS]
          nlinarith [htotal]

lemma fair_nonneg {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (i : Fin n) : 0 ≤ fairSelProb Q j A i := by
  unfold fairSelProb
  by_cases hi : i ∉ A
  · simp [hi]
  rw [if_neg hi]
  by_cases h1 : A.card = 1
  · simp [h1]
  rw [if_neg h1]
  by_cases hS : ∑ k, Q k j = 0
  · rw [if_pos hS]
    positivity
  · rw [if_neg hS]
    have hcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨i, not_not.mp hi⟩
    have hcast : (1 : ℝ) ≤ A.card := by exact_mod_cast hcard
    have hden : 0 ≤ (A.card : ℝ) - 1 := by linarith
    have hsum : 0 ≤ ∑ k, Q k j := Finset.sum_nonneg (fun k _ => hQ k)
    exact mul_nonneg (one_div_nonneg.mpr hsum)
      (add_nonneg (div_nonneg (Finset.sum_nonneg (fun k _ => hQ k)) hden)
        (div_nonneg (Finset.sum_nonneg (fun k _ => hQ k)) (Nat.cast_nonneg _)))

lemma fair_ennreal_sum {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (hA : A.Nonempty) :
    (∑ i, ENNReal.ofReal (fairSelProb Q j A i)) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => fair_nonneg Q j hQ A i), fair_sum Q j A hA]
  norm_num

lemma fairSelect_some {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (hA : A.Nonempty) (i : Fin n) :
    (fairSelect Q j A (some i)).toReal = fairSelProb Q j A i := by
  have hnorm := fair_ennreal_sum Q j hQ A hA
  simp only [fairSelect, dif_pos hnorm, PMF.map_apply, PMF.ofFintype_apply, Option.some.injEq]
  simp [eq_comm, fair_nonneg Q j hQ A i]

lemma fairSelect_empty {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m) :
    fairSelect Q j ∅ = PMF.pure none := by
  simp [fairSelect, fairSelProb, ConsumerUtilityApprox.UnitDemand.uniformOn]

end Utility7.FairProof
end

-- Source module: Solutions.ConsumerUtilityOGD
section

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
end

-- Source module: Solutions.ConsumerUtilityOGDRequests
section

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
end

-- Source module: Solutions.ConsumerUtilityLotteryCosts
section

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
end

-- Source module: Solutions.Utility7ServicePMF
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma service_coin_apply {n : ℕ} (p : ℝ) (s : Option (Fin n)) (i : Fin n) :
    ((coin p).map (fun serve => if serve then s else none)) (some i) =
      if some i = s then coin p true else 0 := by
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_bool, if_true, if_false,
    Bool.false_eq_true, Option.some_ne_none, ite_false, add_zero]

lemma service_apply {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (A : Finset (Fin n)) (p : ℝ) (i : Fin n) :
    ((fairSelect Q j A).bind (fun s =>
      (coin p).map (fun serve => if serve then s else none))) (some i) =
      fairSelect Q j A (some i) * coin p true := by
  rw [PMF.bind_apply]
  simp_rw [service_coin_apply, mul_ite, mul_zero]
  simp only [tsum_ite_eq']

lemma service_probability {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (hA : A.Nonempty) (p : ℝ) (i : Fin n) :
    (((fairSelect Q j A).bind (fun s =>
      (coin p).map (fun serve => if serve then s else none))) (some i)).toReal =
      fairSelProb Q j A i * clamp01 p := by
  rw [service_apply, ENNReal.toReal_mul, FairProof.fairSelect_some Q j hQ A hA i,
    ConsumerUtilityApprox.UnitDemand.OGDProof.coin_true_toReal]

lemma service_probability_all {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (p : ℝ) (i : Fin n) :
    (((fairSelect Q j A).bind (fun s =>
      (coin p).map (fun serve => if serve then s else none))) (some i)).toReal =
      fairSelProb Q j A i * clamp01 p := by
  by_cases hA : A.Nonempty
  · exact service_probability Q j hQ A hA p i
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [service_apply, Utility7.FairProof.fairSelect_empty]
    simp [fairSelProb]

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7PMFBindExpectation
section

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
end

-- Source module: Solutions.Utility7MechanismMix
section

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
end

-- Source module: Solutions.Utility7MixtureIC
section

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
end

-- Source module: Solutions.ConsumerUtilityLotteryMeasurable
section

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
end

-- Source module: Solutions.ConsumerUtilityLotteryExpectation
section

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
end

-- Source module: Solutions.Utility7LotteryIC
section

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
end

-- Source module: Solutions.Utility7FixedPrice
section

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
end

-- Source module: Solutions.Utility7MechanismSafety
section

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
end

-- Source module: Solutions.Utility7RequestIC
section

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
end

-- Source module: Solutions.Utility7AllocationMeasurable
section

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
end

-- Source module: Solutions.Utility7RequestPattern
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma prod_erase_as_prod {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∏ k ∈ Finset.univ.erase i, f k) = ∏ k, if k = i then 1 else f k := by
  have h := Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
    (fun k => if k = i then (1 : ℝ) else f k) (Finset.mem_univ i)
  calc
    _ = ∏ k ∈ Finset.univ.erase i, if k = i then (1 : ℝ) else f k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_erase.mp hk).1]
    _ = _ := by simpa only [ite_true, mul_one] using h

noncomputable def requestPattern {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (A : Finset (Fin n)) (v : Profile n m) : ℝ :=
  ∏ k ∈ Finset.univ.erase i,
    if k ∈ A then (requestMech D k).alloc (v k) j else 1 - (requestMech D k).alloc (v k) j

lemma requestPattern_bounds {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (A : Finset (Fin n)) (v : Profile n m) :
    0 ≤ requestPattern D i j A v ∧ requestPattern D i j A v ≤ 1 := by
  have hf : ∀ k : Fin n, 0 ≤ (if k ∈ A then (requestMech D k).alloc (v k) j
      else 1 - (requestMech D k).alloc (v k) j) ∧
      (if k ∈ A then (requestMech D k).alloc (v k) j
      else 1 - (requestMech D k).alloc (v k) j) ≤ 1 := by
    intro k
    have h := ConsumerUtilityApprox.UnitDemand.OGDProof.alloc_mem_unit_interval
      (requestMech D k) (v k) j
    split_ifs <;> constructor <;> linarith
  exact ⟨Finset.prod_nonneg (fun k _ => (hf k).1),
    Finset.prod_le_one (fun k _ => (hf k).1) (fun k _ => (hf k).2)⟩

lemma measurable_requestPattern {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (A : Finset (Fin n)) : Measurable (requestPattern D i j A) := by
  unfold requestPattern
  apply Finset.measurable_prod
  intro k _
  split_ifs
  · exact (measurable_request_alloc D k j).comp (measurable_pi_apply k)
  · exact measurable_const.sub
      ((measurable_request_alloc D k j).comp (measurable_pi_apply k))

lemma integrable_requestPattern {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (i : Fin n) (j : Fin m) (A : Finset (Fin n)) :
    Integrable (requestPattern D i j A) I.profileLaw := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_requestPattern D i j A).aestronglyMeasurable
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (requestPattern_bounds D i j A v).1]
  exact (requestPattern_bounds D i j A v).2

lemma requestPattern_integral {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (i : Fin n) (j : Fin m) (A : Finset (Fin n)) :
    (∫ v, requestPattern D i j A v ∂I.profileLaw) =
      Utility7.FairProof.weight (fun k => D.Q k j) (Finset.univ.erase i) A := by
  unfold requestPattern
  simp_rw [prod_erase_as_prod]
  change (∫ v, ∏ k, (if k = i then (1 : ℝ) else
    if k ∈ A then (requestMech D k).alloc (v k) j
      else 1 - (requestMech D k).alloc (v k) j)
      ∂Measure.pi (fun k => I.buyerLaw k)) = _
  rw [integral_fintype_prod_eq_prod (fun k (w : Fin m → ℝ≥0) =>
    if k = i then (1 : ℝ) else if k ∈ A then (requestMech D k).alloc w j
      else 1 - (requestMech D k).alloc w j)]
  unfold Utility7.FairProof.weight
  rw [prod_erase_as_prod]
  apply Finset.prod_congr rfl
  intro k _
  by_cases hki : k = i
  · simp [hki]
  · simp only [if_neg hki]
    by_cases hkA : k ∈ A
    · simp only [if_pos hkA]
      exact (announced_eq_request_mean I D hQ k j).symm
    · simp only [if_neg hkA]
      rw [integral_sub (integrable_const _) (integrable_request_alloc D k j _)]
      simp only [integral_const, probReal_univ, one_smul]
      rw [← announced_eq_request_mean I D hQ k j]

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ContentionParameters
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

lemma rand_alloc_bounds {n m : ℕ} (M : RandMech n m) (v : Profile n m)
    (i : Fin n) (j : Fin m) : 0 ≤ M.reduced.x v i j ∧ M.reduced.x v i j ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hh : (M v).toOuterMeasure {ω | ω.1 i = some j} ≤ (1 : ℝ≥0∞) := by
    rw [PMF.toOuterMeasure_apply]
    exact (ENNReal.tsum_le_tsum (fun ω => Set.indicator_apply_le (fun _ => le_rfl))).trans_eq
      (M v).tsum_coe
  exact (ENNReal.toReal_mono (by norm_num) hh).trans_eq (by norm_num)

lemma exAnte_bounds {n m : ℕ} (I : Instance n m) (M : RandMech n m)
    (i : Fin n) (j : Fin m) :
    0 ≤ M.reduced.exAnteAlloc I i j ∧ M.reduced.exAnteAlloc I i j ≤ 1 := by
  constructor
  · exact integral_nonneg (fun v => (rand_alloc_bounds M v i j).1)
  · have hh := integral_mono_of_nonneg
      (ae_of_all I.profileLaw (fun v => (rand_alloc_bounds M v i j).1))
      (integrable_const (1 : ℝ))
      (ae_of_all I.profileLaw (fun v => (rand_alloc_bounds M v i j).2))
    change (∫ v, M.reduced.x v i j ∂I.profileLaw) ≤ 1
    simpa only [integral_const, probReal_univ, one_smul] using hh

lemma clamp01_eq_self (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : clamp01 x = x := by
  simp only [clamp01, min_eq_left hx.2, max_eq_right hx.1]

lemma announced_bounds {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j) :
    ∀ i j, 0 ≤ D.Q i j ∧ D.Q i j ≤ 1 := by
  intro i j
  rw [hQ]
  exact exAnte_bounds I D.preLaw i j

lemma announced_clamp {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j) : D.Q' = D.Q := by
  funext i j
  exact clamp01_eq_self _ (announced_bounds I D hQ i j)

lemma service_parameters {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (I : Instance n m) (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j) :
    ∀ j, 0 ≤ D.σ j ∧ D.σ j ≤ 1 ∧
      clamp01 (D.σ j) = D.σ j ∧
      D.σ j * selectionConst D.Q j = 1 - Real.exp (-1) := by
  have ha : 0 < 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hf : ∀ j, ∑ i, D.Q i j ≤ 1 := by
    intro j
    simpa only [hQ] using hfeas j
  intro j
  have hc := (FairProof.eq_5_11 hn hm D.Q (announced_bounds I D hQ) hf j ⟨0, hn⟩).2
  have hcpos : 0 < selectionConst D.Q j := ha.trans_le hc
  have hs0 : 0 ≤ D.σ j := by rw [hσ]; exact div_nonneg ha.le hcpos.le
  have hs1 : D.σ j ≤ 1 := by rw [hσ]; exact (div_le_one hcpos).mpr hc
  refine ⟨hs0, hs1, clamp01_eq_self _ ⟨hs0, hs1⟩, ?_⟩
  rw [hσ, div_mul_cancel₀ _ hcpos.ne']

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7FairResponse
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma fair_weight_condition {n m : ℕ} (Q : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (i : Fin n) (j : Fin m) :
    (∑ A : Finset (Fin n), Utility7.FairProof.weight r Finset.univ A * fairSelProb Q j A i) =
      r i * ∑ A ∈ (Finset.univ.erase i).powerset,
        Utility7.FairProof.weight r (Finset.univ.erase i) A * fairSelProb Q j (insert i A) i := by
  rw [← Finset.powerset_univ]
  have hu : (Finset.univ : Finset (Fin n)) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  conv_lhs => rw [hu]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ)]
  have hz : (∑ A ∈ (Finset.univ.erase i).powerset,
      Utility7.FairProof.weight r (insert i (Finset.univ.erase i)) A * fairSelProb Q j A i) = 0 := by
    apply Finset.sum_eq_zero
    intro A hA
    have hi : i ∉ A := fun hi => Finset.notMem_erase i Finset.univ
      (Finset.mem_powerset.mp hA hi)
    simp only [fairSelProb, if_pos hi, mul_zero]
  rw [hz, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Utility7.FairProof.weight_insert_present r (Finset.notMem_erase i Finset.univ)
    (Finset.mem_powerset.mp hA)]
  ring

noncomputable def fairResponse {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (v : Profile n m) : ℝ :=
  ∑ A ∈ (Finset.univ.erase i).powerset,
    requestPattern D i j A v * fairSelProb D.Q' j (insert i A) i

lemma requestPattern_update {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (A : Finset (Fin n)) (v : Profile n m) (w : Fin m → ℝ≥0) :
    requestPattern D i j A (Function.update v i w) = requestPattern D i j A v := by
  unfold requestPattern
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

lemma fairResponse_update {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (j : Fin m) (v : Profile n m) (w : Fin m → ℝ≥0) :
    fairResponse D i j (Function.update v i w) = fairResponse D i j v := by
  unfold fairResponse
  simp_rw [requestPattern_update]

lemma integrable_fairResponse {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (i : Fin n) (j : Fin m) : Integrable (fairResponse D i j) I.profileLaw := by
  exact integrable_finsetSum _ (fun A _ => (integrable_requestPattern I D i j A).mul_const _)

lemma fairResponse_integral {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (I : Instance n m) (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (i : Fin n) (j : Fin m) :
    (∫ v, fairResponse D i j v ∂I.profileLaw) = selectionConst D.Q j := by
  unfold fairResponse
  rw [integral_finsetSum _ (fun A _ => (integrable_requestPattern I D i j A).mul_const _)]
  simp_rw [integral_mul_const, requestPattern_integral I D hQ, announced_clamp I D hQ]
  exact (Utility7.FairProof.eq_5_11 hn hm D.Q (announced_bounds I D hQ)
    (fun j => by simpa only [hQ] using hfeas j) j i).1

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ContentionAllocation
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma pmf_event_mean {α β : Type} [DecidableEq β] (p : PMF α) (f : α → β) (b : β) :
    (∑' a, (p a).toReal * (if f a = b then (1 : ℝ) else 0)) = ((p.map f) b).toReal := by
  rw [mean_nonnegative p _ (by intro a _; split_ifs <;> norm_num), PMF.map_apply]
  congr 1
  apply tsum_congr
  intro a
  by_cases h : f a = b
  · simp [h]
  · simp [h, Ne.symm h]

noncomputable def itemService {n m : ℕ} (D : MechDescription n m)
    (req : Fin n → Request m) (j : Fin m) : PMF (Option (Fin n)) :=
  (fairSelect D.Q' j (MechDescription.requesters req j)).bind fun s =>
    (coin (D.σ j)).map fun serve => if serve then s else none

noncomputable def selectionLaw {n m : ℕ} (D : MechDescription n m)
    (req : Fin n → Request m) : PMF (Fin m → Option (Fin n)) :=
  indep m (itemService D req)

lemma service_allocation_mean {n m : ℕ} (D : MechDescription n m)
    (req : Fin n → Request m) (i : Fin n) (j : Fin m) :
    (∑' sel, (selectionLaw D req sel).toReal *
      (if sel j = some i then (1 : ℝ) else 0)) =
      fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j) := by
  calc
    _ = (((selectionLaw D req).map (fun sel => sel j)) (some i)).toReal :=
      pmf_event_mean (selectionLaw D req) (fun sel => sel j) (some i)
    _ = _ := ?_
  rw [selectionLaw, indep_eval]
  exact service_probability_all D.Q' j (by
    intro k
    unfold MechDescription.Q' clamp01
    exact le_max_left _ _) _ _ _

lemma served_allocation_mean {n m : ℕ} (D : MechDescription n m)
    (req : Fin n → Request m) (i : Fin n) (j : Fin m) :
    (∑' sel, (selectionLaw D req sel).toReal *
      (if (servedOutcome req sel).1 i = some j then (1 : ℝ) else 0)) =
      fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j) := by
  by_cases hreq : (req i).map Prod.fst = some j
  · have he : ∀ sel, (servedOutcome req sel).1 i = some j ↔ sel j = some i := by
      intro sel
      cases hr : req i with
      | none => simp [hr] at hreq
      | some a =>
        obtain ⟨k, p⟩ := a
        have hk : k = j := by simpa [hr] using hreq
        subst k
        simp [servedOutcome, hr]
    simp_rw [he]
    exact service_allocation_mean D req i j
  · have hz : fairSelProb D.Q' j (MechDescription.requesters req j) i = 0 := by
      have hi : i ∉ MechDescription.requesters req j := by
        simpa only [MechDescription.requesters, Finset.mem_filter, Finset.mem_univ,
          true_and] using hreq
      simp only [fairSelProb, if_pos hi]
    rw [hz, zero_mul]
    calc
      _ = ∑' sel : Fin m → Option (Fin n), (0 : ℝ) := by
        apply tsum_congr
        intro sel
        have hn : (servedOutcome req sel).1 i ≠ some j := by
          intro h
          cases hr : req i with
          | none => simp [servedOutcome, hr] at h
          | some a =>
            obtain ⟨k, p⟩ := a
            simp only [servedOutcome, hr] at h
            split_ifs at h with hs
            · exact hreq (by simpa [hr] using h)
        simp [hn]
      _ = 0 := tsum_zero

lemma law_allocation_as_mean {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) (j : Fin m) :
    D.law.reduced.x v i j = ∑' req, (indep n (fun k => D.request k (v k)) req).toReal *
      (fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j)) := by
  have he := pmf_event_mean (D.law v) (fun (ω : Outcome n m) => ω.1 i) (some j)
  have hx : D.law.reduced.x v i j =
      (((D.law v).map (fun (ω : Outcome n m) => ω.1 i)) (some j)).toReal := by
    change ((D.law v).toOuterMeasure {ω | ω.1 i = some j}).toReal = _
    rw [PMF.map_apply, PMF.toOuterMeasure_apply]
    congr 1
    apply tsum_congr
    intro ω
    by_cases h : ω.1 i = some j
    · simp [Set.indicator, h]
    · simp [Set.indicator, h, Ne.symm h]
  rw [hx, ← he]
  unfold MechDescription.law
  change (∑' ω, (((indep n (fun k => D.request k (v k))).bind fun req =>
    (selectionLaw D req).map (servedOutcome req)) ω).toReal *
      (if ω.1 i = some j then (1 : ℝ) else 0)) = _
  rw [mean_bind _ _ _ 1 (by intro a ha b hb; split_ifs <;> norm_num)]
  apply tsum_congr
  intro req
  rw [mean_map _ _ _ (by intro sel _; split_ifs <;> norm_num)]
  rw [served_allocation_mean]

lemma law_allocation_conditioned {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) (j : Fin m) :
    D.law.reduced.x v i j =
      (requestMech D i).alloc (v i) j * clamp01 (D.σ j) * fairResponse D i j v := by
  have hn : ∀ A, 0 ≤ fairSelProb D.Q' j A i := fun A =>
    Utility7.FairProof.fair_nonneg D.Q' j (fun k => le_max_left _ _) A i
  rw [law_allocation_as_mean]
  calc
    _ = (∑' req, (indep n (fun k => D.request k (v k)) req).toReal *
        fairSelProb D.Q' j (MechDescription.requesters req j) i) * clamp01 (D.σ j) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro req
      ring
    _ = (∑ A : Finset (Fin n), Utility7.FairProof.weight
        (fun k => (requestMech D k).alloc (v k) j) Finset.univ A *
          fairSelProb D.Q' j A i) * clamp01 (D.σ j) := by
      rw [mean_requesters D v j (fun A => fairSelProb D.Q' j A i) hn]
      rfl
    _ = _ := by
      rw [fair_weight_condition]
      change ((requestMech D i).alloc (v i) j * fairResponse D i j v) *
        clamp01 (D.σ j) = _
      ring

theorem interim_allocation_scaled {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (I : Instance n m) (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j)
    (i : Fin n) (w : Fin m → ℝ≥0) (j : Fin m) :
    D.law.reduced.interimAlloc I i w j =
      (1 - Real.exp (-1)) * D.preLaw.reduced.interimAlloc I i w j := by
  rw [preLaw_interimAllocation]
  unfold RMech.interimAlloc
  simp_rw [law_allocation_conditioned, Function.update_self, fairResponse_update]
  rw [integral_const_mul, fairResponse_integral hn hm I D hfeas hQ]
  have hs := service_parameters hn hm I D hfeas hQ hσ j
  rw [hs.2.2.1]
  calc
    _ = (requestMech D i).alloc w j * (D.σ j * selectionConst D.Q j) := by ring
    _ = _ := by rw [hs.2.2.2]; ring

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7IndependentExpectation
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

lemma ennreal_mean_indep_prod {α : Type} (n : ℕ) (p : Fin n → PMF α)
    (g : Fin n → α → ℝ≥0∞) :
    (∑' a, indep n p a * ∏ i, g i (a i)) = ∏ i, ∑' a, p i a * g i a := by
  classical
  induction n with
  | zero =>
    simp [indep, PMF.pure_apply]
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [indep, ennreal_mean_bind]
    simp_rw [ennreal_mean_map, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hm (a : α) :
        (∑' b, indep n (fun i => p i.succ) b *
          (g 0 a * ∏ i, g i.succ (b i))) =
        g 0 a * ∏ i : Fin n, ∑' b, p i.succ b * g i.succ b := by
      calc
        _ = g 0 a * (∑' b, indep n (fun i => p i.succ) b * ∏ i, g i.succ (b i)) := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro b
          ring
        _ = _ := by rw [ih]
    simp_rw [hm]
    simp_rw [← mul_assoc]
    rw [ENNReal.tsum_mul_right]

lemma mean_indep_prod {α : Type} (n : ℕ) (p : Fin n → PMF α) (f : Fin n → α → ℝ)
    (hf : ∀ i a, 0 ≤ f i a) :
    (∑' a, (indep n p a).toReal * ∏ i, f i (a i)) =
      ∏ i, ∑' a, (p i a).toReal * f i a := by
  rw [mean_nonnegative _ _ (by
    intro a _
    exact Finset.prod_nonneg (fun i _ => hf i (a i)))]
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hf i _)]
  rw [ennreal_mean_indep_prod n p (fun i a => ENNReal.ofReal (f i a)), ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact (mean_nonnegative (p i) (f i) (fun a _ => hf i a)).symm

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7PatternIndicator
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def patternIndicator {κ : Type} [DecidableEq κ] (s A : Finset κ)
    (P : κ → Prop) [DecidablePred P] : ℝ :=
  ∏ k ∈ s, if k ∈ A then (if P k then 1 else 0) else (if P k then 0 else 1)

lemma patternIndicator_eq {κ : Type} [DecidableEq κ] (s A : Finset κ)
    (P : κ → Prop) [DecidablePred P] (hA : A ⊆ s) :
    patternIndicator s A P = if A = s.filter P then 1 else 0 := by
  by_cases he : A = s.filter P
  · subst A
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro k hk
    by_cases hP : P k <;> simp [Finset.mem_filter, hk, hP]
  · rw [if_neg he]
    have hex : ∃ k ∈ s, ¬(k ∈ A ↔ P k) := by
      by_contra! h
      apply he
      ext k
      constructor
      · intro hk
        exact Finset.mem_filter.mpr ⟨hA hk, (h k (hA hk)).mp hk⟩
      · intro hk
        exact (h k (Finset.mem_filter.mp hk).1).mpr (Finset.mem_filter.mp hk).2
    obtain ⟨k, hk, hbad⟩ := hex
    apply Finset.prod_eq_zero hk
    by_cases hkA : k ∈ A <;> by_cases hP : P k <;> simp_all

lemma sum_patternIndicator {κ : Type} [DecidableEq κ] (s : Finset κ)
    (P : κ → Prop) [DecidablePred P] (G : Finset κ → ℝ) :
    (∑ A ∈ s.powerset, patternIndicator s A P * G A) = G (s.filter P) := by
  have hs : s.filter P ∈ s.powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  calc
    _ = ∑ A ∈ s.powerset, (if A = s.filter P then G A else 0) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [patternIndicator_eq s A P (Finset.mem_powerset.mp hA)]
      split_ifs <;> simp
    _ = _ := by simp [hs]

lemma marked_pattern_identity {α : Type} {n : ℕ} (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)]
    (i : Fin n) (f : α → ℝ) (hf : ∀ a, ¬P i a → f a = 0)
    (G : Finset (Fin n) → ℝ) (a : Fin n → α) :
    f (a i) * G (Finset.univ.filter (fun k => P k (a k))) =
      ∑ A ∈ (Finset.univ.erase i).powerset,
        (∏ k, if k = i then f (a k) else
          if k ∈ A then (if P k (a k) then 1 else 0) else (if P k (a k) then 0 else 1)) *
          G (insert i A) := by
  have hprod (A : Finset (Fin n)) :
      (∏ k, if k = i then f (a k) else
        if k ∈ A then (if P k (a k) then (1 : ℝ) else 0) else (if P k (a k) then 0 else 1)) =
      f (a i) * patternIndicator (Finset.univ.erase i) A (fun k => P k (a k)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [if_neg (Finset.mem_erase.mp hk).1]
  simp_rw [hprod, mul_assoc]
  rw [← Finset.mul_sum, sum_patternIndicator]
  by_cases hi : P i (a i)
  · congr 1
    apply congrArg G
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_erase]
    by_cases hk : k = i
    · subst k; simp [hi]
    · simp [hk, Ne.symm hk]
  · rw [hf (a i) hi, zero_mul, zero_mul]

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7MarkedExpectation
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def markedFactor {α : Type} {n : ℕ} (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)]
    (i : Fin n) (f : α → ℝ) (A : Finset (Fin n)) (k : Fin n) (a : α) : ℝ :=
  if k = i then f a else if k ∈ A then (if P k a then 1 else 0) else (if P k a then 0 else 1)

lemma markedFactor_nonneg {α : Type} {n : ℕ} (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)]
    (i : Fin n) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (A : Finset (Fin n))
    (k : Fin n) (a : α) : 0 ≤ markedFactor P i f A k a := by
  unfold markedFactor
  split_ifs <;> first | exact hf a | norm_num

lemma marked_product_eq {α : Type} {n : ℕ} (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)]
    (i : Fin n) (f : α → ℝ) (A : Finset (Fin n)) (a : Fin n → α) :
    (∏ k, markedFactor P i f A k (a k)) =
      f (a i) * patternIndicator (Finset.univ.erase i) A (fun k => P k (a k)) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [markedFactor, ite_true]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [if_neg (Finset.mem_erase.mp hk).1]

lemma marked_product_bounds {α : Type} {n : ℕ} (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)]
    (i : Fin n) (f : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ B) (A : Finset (Fin n))
    (hA : A ⊆ Finset.univ.erase i) (a : Fin n → α) :
    0 ≤ (∏ k, markedFactor P i f A k (a k)) ∧
      (∏ k, markedFactor P i f A k (a k)) ≤ B := by
  rw [marked_product_eq, patternIndicator_eq _ _ _ hA]
  split_ifs <;> simp_all

lemma mean_marked_pattern {α : Type} {n : ℕ} (p : Fin n → PMF α)
    (P : Fin n → α → Prop) [∀ k a, Decidable (P k a)] (i : Fin n) (f : α → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ B)
    (hzero : ∀ a, ¬P i a → f a = 0)
    (G : Finset (Fin n) → ℝ) (hG : ∀ A, 0 ≤ G A ∧ G A ≤ 1) :
    (∑' a, (indep n p a).toReal * (f (a i) * G (Finset.univ.filter (fun k => P k (a k))))) =
      (∑' a, (p i a).toReal * f a) *
        ∑ A ∈ (Finset.univ.erase i).powerset,
          (∏ k ∈ Finset.univ.erase i, ∑' a, (p k a).toReal *
            (if k ∈ A then (if P k a then 1 else 0) else (if P k a then 0 else 1))) *
            G (insert i A) := by
  let s := (Finset.univ.erase i).powerset
  let F (A : Finset (Fin n)) (a : Fin n → α) := ∏ k, markedFactor P i f A k (a k)
  have hsum (A : Finset (Fin n)) (hA : A ∈ s) :
      Summable (fun a => (indep n p a).toReal * (F A a * G (insert i A))) := by
    apply nonnegative_mean_summable (indep n p) _ B
    intro a _
    have hb := marked_product_bounds P i f B hB hf A (Finset.mem_powerset.mp hA) a
    exact ⟨mul_nonneg hb.1 (hG _).1,
      (mul_le_mul_of_nonneg_left (hG _).2 hb.1).trans (by simpa only [mul_one] using hb.2)⟩
  have hmean (A : Finset (Fin n)) :
      (∑' a, (indep n p a).toReal * F A a) =
      (∑' a, (p i a).toReal * f a) *
        ∏ k ∈ Finset.univ.erase i, ∑' a, (p k a).toReal *
          (if k ∈ A then (if P k a then 1 else 0) else (if P k a then 0 else 1)) := by
    rw [mean_indep_prod n p (markedFactor P i f A)
      (markedFactor_nonneg P i f (fun a => (hf a).1) A)]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [markedFactor, ite_true]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    simp only [if_neg (Finset.mem_erase.mp hk).1]
  calc
    _ = ∑' a, (indep n p a).toReal * ∑ A ∈ s, F A a * G (insert i A) := by
      apply tsum_congr
      intro a
      congr 1
      exact marked_pattern_identity P i f hzero G a
    _ = ∑ A ∈ s, ∑' a, (indep n p a).toReal * (F A a * G (insert i A)) := by
      simp_rw [Finset.mul_sum]
      exact Summable.tsum_finsetSum hsum
    _ = _ := by
      simp_rw [← mul_assoc, tsum_mul_right, hmean]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      ring

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ItemPayments
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def cappedItemPayment {m : ℕ} (w : Fin m → ℝ≥0) (j : Fin m) : Request m → ℝ
  | none => 0
  | some (k, p) => if k = j then max 0 (min p (w j : ℝ)) else 0

lemma cappedItemPayment_bounds {m : ℕ} (w : Fin m → ℝ≥0) (j : Fin m) (r : Request m) :
    0 ≤ cappedItemPayment w j r ∧ cappedItemPayment w j r ≤ w j := by
  cases r with
  | none => simp [cappedItemPayment]
  | some a =>
    obtain ⟨k, p⟩ := a
    simp only [cappedItemPayment]
    split_ifs
    · exact ⟨le_max_left _ _, max_le (w j).coe_nonneg (min_le_right _ _)⟩
    · simp

lemma cappedItemPayment_zero {m : ℕ} (w : Fin m → ℝ≥0) (j : Fin m) (r : Request m)
    (hr : ¬r.map Prod.fst = some j) : cappedItemPayment w j r = 0 := by
  cases r with
  | none => rfl
  | some a =>
    obtain ⟨k, p⟩ := a
    have hk : k ≠ j := by simpa using hr
    simp [cappedItemPayment, hk]

lemma cappedItemPayment_valid {m : ℕ} (w : Fin m → ℝ≥0) (j k : Fin m) (p : ℝ)
    (hp : 0 ≤ p ∧ p ≤ w k) : cappedItemPayment w j (some (k, p)) = if k = j then p else 0 := by
  by_cases hk : k = j
  · subst k
    simp [cappedItemPayment, min_eq_left hp.2, max_eq_right hp.1]
  · simp [cappedItemPayment, hk]

lemma fair_probability_bounds {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (hQ : ∀ k, 0 ≤ Q k j) (A : Finset (Fin n)) (i : Fin n) :
    0 ≤ fairSelProb Q j A i ∧ fairSelProb Q j A i ≤ 1 := by
  refine ⟨Utility7.FairProof.fair_nonneg Q j hQ A i, ?_⟩
  by_cases hA : A.Nonempty
  · have hs := Finset.single_le_sum
      (fun k _ => Utility7.FairProof.fair_nonneg Q j hQ A k) (Finset.mem_univ i)
    rwa [Utility7.FairProof.fair_sum Q j A hA] at hs
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [fairSelProb]

noncomputable def requestItemPayment {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (w : Fin m → ℝ≥0) (j : Fin m) : ℝ :=
  ∑' r, (D.request i w r).toReal * cappedItemPayment w j r

lemma request_item_payments_sum {n m : ℕ} (D : MechDescription n m) (i : Fin n)
    (w : Fin m → ℝ≥0) : (requestMech D i).pay w = ∑ j, requestItemPayment D i w j := by
  unfold requestMech SBRand.pay
  rw [mean_map _ Request.toOutcome Prod.snd (by
    intro r hr
    cases r with
    | none => rfl
    | some a =>
      obtain ⟨j, p⟩ := a
      exact (request_valid D i w j p hr).1)]
  have he : ∀ r ∈ (D.request i w).support,
      (Request.toOutcome r).2 = ∑ j, cappedItemPayment w j r := by
    intro r hr
    cases r with
    | none => simp [Request.toOutcome, cappedItemPayment]
    | some a =>
      obtain ⟨k, p⟩ := a
      simp_rw [cappedItemPayment_valid w _ k p (request_valid D i w k p hr)]
      simp [Request.toOutcome]
  calc
    _ = ∑' r, (D.request i w r).toReal * ∑ j, cappedItemPayment w j r := by
      apply tsum_congr
      intro r
      by_cases hr : D.request i w r = 0
      · simp [hr]
      · rw [he r (((D.request i w).mem_support_iff r).mpr hr)]
    _ = _ := by
      simp_rw [Finset.mul_sum]
      exact Summable.tsum_finsetSum (fun j _ => nonnegative_mean_summable
        (D.request i w) (cappedItemPayment w j) (w j) (fun r _ => cappedItemPayment_bounds w j r))

lemma request_pattern_coordinate_mean {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (j : Fin m) (A : Finset (Fin n)) (k : Fin n) :
    (∑' r, (D.request k (v k) r).toReal *
      (if k ∈ A then (if r.map Prod.fst = some j then (1 : ℝ) else 0)
      else (if r.map Prod.fst = some j then 0 else 1))) =
      if k ∈ A then (requestMech D k).alloc (v k) j
        else 1 - (requestMech D k).alloc (v k) j := by
  by_cases hk : k ∈ A
  · simp only [if_pos hk]
    have h := pmf_event_mean (D.request k (v k)) (requestsItem j) true
    rw [request_probability] at h
    convert h using 1
    apply tsum_congr
    intro r
    by_cases hr : r.map Prod.fst = some j <;> simp [requestsItem, hr]
  · simp only [if_neg hk]
    have h := pmf_event_mean (D.request k (v k)) (requestsItem j) false
    rw [bool_false_probability, request_probability] at h
    convert h using 1
    apply tsum_congr
    intro r
    by_cases hr : r.map Prod.fst = some j <;> simp [requestsItem, hr]

lemma mean_request_item_fair {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) (j : Fin m) :
    (∑' req, (indep n (fun k => D.request k (v k)) req).toReal *
      (cappedItemPayment (v i) j (req i) *
        fairSelProb D.Q' j (MechDescription.requesters req j) i)) =
      requestItemPayment D i (v i) j * fairResponse D i j v := by
  have h := mean_marked_pattern (fun k => D.request k (v k))
    (fun _ r => r.map Prod.fst = some j) i (cappedItemPayment (v i) j) (v i j)
      (v i j).coe_nonneg (cappedItemPayment_bounds (v i) j)
      (cappedItemPayment_zero (v i) j) (fun A => fairSelProb D.Q' j A i)
      (fun A => fair_probability_bounds D.Q' j (fun _ => le_max_left _ _) A i)
  simp_rw [request_pattern_coordinate_mean D v j] at h
  exact h

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ContentionPayment
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

attribute [local instance] Classical.propDecidable Classical.decEq

lemma served_payment_bounds {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (req : Fin n → Request m) (hr : req ∈ (indep n (fun k => D.request k (v k))).support)
    (sel : Fin m → Option (Fin n)) (i : Fin n) :
    0 ≤ (servedOutcome req sel).2 i ∧ (servedOutcome req sel).2 i ≤ ∑ j, (v i j : ℝ) := by
  have hri := indep_support_coordinate _ _ hr i
  cases he : req i with
  | none =>
    simp only [servedOutcome, he, le_refl, true_and]
    exact Finset.sum_nonneg (fun j _ => (v i j).coe_nonneg)
  | some a =>
    obtain ⟨j, p⟩ := a
    rw [he] at hri
    have hp := request_valid D i (v i) j p hri
    have hv : (v i j : ℝ) ≤ ∑ k, (v i k : ℝ) :=
      Finset.single_le_sum (fun k _ => (v i k).coe_nonneg) (Finset.mem_univ j)
    simp only [servedOutcome, he]
    split_ifs
    · exact ⟨hp.1, hp.2.trans hv⟩
    · simp only [le_refl, true_and]
      exact Finset.sum_nonneg (fun k _ => (v i k).coe_nonneg)

lemma served_payment_mean {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (req : Fin n → Request m) (hr : req ∈ (indep n (fun k => D.request k (v k))).support)
    (i : Fin n) :
    (∑' sel, (selectionLaw D req sel).toReal * (servedOutcome req sel).2 i) =
      ∑ j, cappedItemPayment (v i) j (req i) *
        fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j) := by
  have hri := indep_support_coordinate _ _ hr i
  cases he : req i with
  | none => simp [servedOutcome, he, cappedItemPayment]
  | some a =>
    obtain ⟨k, p⟩ := a
    rw [he] at hri
    have hp := request_valid D i (v i) k p hri
    simp_rw [cappedItemPayment_valid (v i) _ k p hp]
    have hsum : (∑ j, (if k = j then p else 0) *
      fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j)) =
      p * fairSelProb D.Q' k (MechDescription.requesters req k) i * clamp01 (D.σ k) := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hsum]
    calc
      _ = (∑' sel, (selectionLaw D req sel).toReal *
          (if sel k = some i then (1 : ℝ) else 0)) * p := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro sel
        by_cases hs : sel k = some i <;> simp [servedOutcome, he, hs] <;> ring
      _ = _ := by rw [service_allocation_mean]; ring

lemma law_payment_as_mean {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) : D.law.reduced.p v i =
      ∑' req, (indep n (fun k => D.request k (v k)) req).toReal *
        ∑ j, cappedItemPayment (v i) j (req i) *
          fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j) := by
  change (∑' ω, (D.law v ω).toReal * ω.2 i) = _
  unfold MechDescription.law
  change (∑' ω, (((indep n (fun k => D.request k (v k))).bind fun req =>
    (selectionLaw D req).map (servedOutcome req)) ω).toReal * ω.2 i) = _
  rw [mean_bind _ _ _ (∑ j, (v i j : ℝ)) (by
    intro req hr ω hω
    obtain ⟨sel, hsel, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hω
    exact served_payment_bounds D v req hr sel i)]
  apply tsum_congr
  intro req
  by_cases hr : indep n (fun k => D.request k (v k)) req = 0
  · simp [hr]
  · have hreq := ((indep n (fun k => D.request k (v k))).mem_support_iff req).mpr hr
    rw [mean_map _ _ _ (fun sel _ => (served_payment_bounds D v req hreq sel i).1)]
    rw [served_payment_mean D v req hreq i]

lemma law_payment_conditioned {n m : ℕ} (D : MechDescription n m) (v : Profile n m)
    (i : Fin n) : D.law.reduced.p v i =
      ∑ j, requestItemPayment D i (v i) j * clamp01 (D.σ j) * fairResponse D i j v := by
  have hs (j : Fin m) : Summable (fun req =>
      (indep n (fun k => D.request k (v k)) req).toReal *
        (cappedItemPayment (v i) j (req i) *
          fairSelProb D.Q' j (MechDescription.requesters req j) i * clamp01 (D.σ j))) := by
    apply nonnegative_mean_summable _ _ (v i j)
    intro req _
    have hf := cappedItemPayment_bounds (v i) j (req i)
    have hg := fair_probability_bounds D.Q' j (fun _ => le_max_left _ _)
      (MechDescription.requesters req j) i
    have hc : 0 ≤ clamp01 (D.σ j) ∧ clamp01 (D.σ j) ≤ 1 := by
      unfold clamp01
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    refine ⟨mul_nonneg (mul_nonneg hf.1 hg.1) hc.1, ?_⟩
    calc
      _ ≤ cappedItemPayment (v i) j (req i) * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hg.2 hf.1) hc.2 hc.1
          (by simpa only [mul_one] using hf.1)
      _ ≤ v i j := by simpa only [mul_one] using hf.2
  rw [law_payment_as_mean]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j _ => hs j)]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (∑' req, (indep n (fun k => D.request k (v k)) req).toReal *
        (cappedItemPayment (v i) j (req i) *
          fairSelProb D.Q' j (MechDescription.requesters req j) i)) * clamp01 (D.σ j) := by
      rw [← tsum_mul_right]
      apply tsum_congr
      intro req
      ring
    _ = _ := by rw [mean_request_item_fair]; ring

theorem interim_payment_scaled {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (I : Instance n m) (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j)
    (i : Fin n) (w : Fin m → ℝ≥0) :
    D.law.reduced.interimPay I i w =
      (1 - Real.exp (-1)) * D.preLaw.reduced.interimPay I i w := by
  rw [preLaw_interimPayment, request_item_payments_sum]
  unfold RMech.interimPay
  simp_rw [law_payment_conditioned, Function.update_self, fairResponse_update]
  rw [integral_finsetSum _ (fun j _ => (integrable_fairResponse I D i j).const_mul _)]
  simp_rw [integral_const_mul, fairResponse_integral hn hm I D hfeas hQ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs := service_parameters hn hm I D hfeas hQ hσ j
  rw [hs.2.2.1]
  calc
    _ = requestItemPayment D i w j * (D.σ j * selectionConst D.Q j) := by ring
    _ = _ := by rw [hs.2.2.2]; ring

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ContentionAssembly
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

/-- Pure assembly from interim identities. The identities and the pre-law BIC
property are separate obligations; this is not the full equation (5.12). -/
lemma interim_utility_scaled {n m : ℕ} (I : Instance n m) (M L : RandMech n m) (a : ℝ)
    (hx : ∀ i w j, M.reduced.interimAlloc I i w j = a * L.reduced.interimAlloc I i w j)
    (hp : ∀ i w, M.reduced.interimPay I i w = a * L.reduced.interimPay I i w)
    (i : Fin n) (v w : Fin m → ℝ≥0) :
    M.reduced.interimUtil I i v w = a * L.reduced.interimUtil I i v w := by
  unfold RMech.interimUtil
  simp_rw [hx, hp]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma utility_scaled {n m : ℕ} (I : Instance n m) (M L : RandMech n m) (a : ℝ)
    (hx : ∀ i w j, M.reduced.interimAlloc I i w j = a * L.reduced.interimAlloc I i w j)
    (hp : ∀ i w, M.reduced.interimPay I i w = a * L.reduced.interimPay I i w) :
    M.U I = a * L.U I := by
  unfold RandMech.U RMech.U
  simp_rw [interim_utility_scaled I M L a hx hp, integral_const_mul]
  exact (Finset.mul_sum _ _ _).symm

lemma eq_5_12_of_interim {n m : ℕ} (I : Instance n m) (D : MechDescription n m)
    (hBIC : D.preLaw.IsBIC I)
    (hx : ∀ i w j, D.law.reduced.interimAlloc I i w j =
      (1 - Real.exp (-1)) * D.preLaw.reduced.interimAlloc I i w j)
    (hp : ∀ i w, D.law.reduced.interimPay I i w =
      (1 - Real.exp (-1)) * D.preLaw.reduced.interimPay I i w) :
    D.law.IsBIC I ∧ D.law.IsExPostIR ∧ D.law.IsMatchingFeasible ∧
      D.law.HasNonnegPayments ∧
      D.law.U I = (1 - Real.exp (-1)) * D.preLaw.U I := by
  have ha : 0 ≤ 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  refine ⟨?_, (realized_ir_and_nonnegative D).1, matching_feasible D,
    (realized_ir_and_nonnegative D).2, utility_scaled I D.law D.preLaw _ hx hp⟩
  intro i v w
  rw [interim_utility_scaled I D.law D.preLaw _ hx hp,
    interim_utility_scaled I D.law D.preLaw _ hx hp]
  exact mul_le_mul_of_nonneg_left (hBIC i v w) ha

end Utility7.ContentionProof
end

-- Source module: Solutions.Utility7ContentionMain
section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open ConsumerUtilityApprox.UnitDemand

namespace Utility7.ContentionProof

theorem eq_5_12 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j) :
    D.law.IsBIC I ∧ D.law.IsExPostIR ∧ D.law.IsMatchingFeasible ∧
      D.law.HasNonnegPayments ∧
      D.law.U I = (1 - Real.exp (-1)) * D.preLaw.U I :=
  eq_5_12_of_interim I D (preLaw_BIC I D)
    (interim_allocation_scaled hn hm I D hfeas hQ hσ)
    (interim_payment_scaled hn hm I D hfeas hQ hσ)

end Utility7.ContentionProof
end

open ConsumerUtilityApprox.UnitDemand

theorem solution {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (I : Instance n m)
    (D : MechDescription n m)
    (hfeas : D.preLaw.reduced.IsExAnteFeasible I)
    (hQ : ∀ i j, D.Q i j = D.preLaw.reduced.exAnteAlloc I i j)
    (hσ : ∀ j, D.σ j = (1 - Real.exp (-1)) / selectionConst D.Q j) :
    D.law.IsBIC I ∧ D.law.IsExPostIR ∧ D.law.IsMatchingFeasible ∧
      D.law.HasNonnegPayments ∧
      D.law.U I = (1 - Real.exp (-1)) * D.preLaw.U I  := Utility7.ContentionProof.eq_5_12 hn hm I D hfeas hQ hσ

#print axioms solution
