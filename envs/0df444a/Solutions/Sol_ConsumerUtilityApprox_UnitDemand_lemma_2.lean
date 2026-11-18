-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T20:25:39.923198+00:00
-- url     : https://prove2.me/submissions/b3ba50b7-29d0-4ef3-b395-0414bb5077a6

import Mathlib
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model

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

-- Source module: Solutions.Utility7MechanismIntegrability
section

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
end

-- Source module: Solutions.Utility7DeletionMonotonic
section

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
end

-- Source module: Solutions.Utility7ResampledProfiles
section

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
end

-- Source module: Solutions.Utility7SingleItemSlice
section

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
end

-- Source module: Solutions.Utility7SingleItemAverage
section

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
end

-- Source module: Solutions.Utility7SingleItemComparison
section

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
end

open ConsumerUtilityApprox.UnitDemand
open MultiItemRev.BundlingOpt
open MeasureTheory
open ProbabilityTheory
open scoped NNReal
open scoped ENNReal

theorem solution {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j) (j : Fin m) :
    deletionLoss (vecLaw G) M j ≤ OPT11 (G j) (q j)  := Utility7.BenchmarkProof.lemma_2 hm G hG M hM q hq j

#print axioms solution
