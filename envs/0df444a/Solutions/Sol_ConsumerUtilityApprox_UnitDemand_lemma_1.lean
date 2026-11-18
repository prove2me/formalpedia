-- Prove2me | solution 1 for ConsumerUtilityApprox.UnitDemand.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T20:09:25.457634+00:00
-- url     : https://prove2.me/submissions/aa50877a-eb7c-4dcc-b15f-ab686e004fcd

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

-- Source module: Solutions.Utility7Overlap
section

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
end

open ConsumerUtilityApprox.UnitDemand
open MultiItemRev.BundlingOpt
open MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {m : ℕ} (hm : 1 ≤ m) (G : Fin m → ProbabilityMeasure ℝ≥0)
    (hG : ∀ j, IsValueLaw (G j)) (M : Mechanism (Fin m)) (hM : IsTruthfulIRNPT M)
    (q : Fin m → ℝ) (hq : ∀ j, qAlloc (vecLaw G) M j ≤ q j)
    (ℓ : Fin m → ℝ) (hℓ : ∀ j, 0 < ℓ j ∧ ℓ j ≤ 1) :
    ∫ vw, min (buyerPayoff M vw.1) (buyerPayoff M vw.2) ∂((vecLaw G).prod (vecLaw G))
      ≤ (∫ v, (⨆ j, ℓ j * (v j : ℝ)) ∂(vecLaw G)) * ∑ j, q j / ℓ j  := Utility7.BenchmarkProof.lemma_1 hm G hG M hM q hq ℓ hℓ

#print axioms solution
