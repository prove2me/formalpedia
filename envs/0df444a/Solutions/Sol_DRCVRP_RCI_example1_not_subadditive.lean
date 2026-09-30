-- Prove2me | solution 1 for DRCVRP.RCI.example1_not_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T09:18:58.279357+00:00
-- url     : https://prove2.me/submissions/d7b879c6-7818-4521-bd13-2a11dc4fc84c

import Definitions.Def_DRCVRP_RCI_Example1
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_MultistageStochastic_RiskFunctional
import Mathlib.Probability.CDF
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 800000
private theorem var_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (τ : ℝ) :
    ENNReal.ofReal α ≤ P {q | X q ≤ τ} ↔ MultistageStochastic.valueAtRisk P X α ≤ τ := by
  haveI : IsProbabilityMeasure (P.map X) := P.isProbabilityMeasure_map hX.aemeasurable
  let F := cdf (P.map X)
  have hf (y : ℝ) : ENNReal.ofReal α ≤ P {q | X q ≤ y} ↔ α ≤ F y := by
    change ENNReal.ofReal α ≤ P (X ⁻¹' Iic y) ↔ α ≤ F y
    rw [← Measure.map_apply hX measurableSet_Iic, ← ofReal_cdf]
    exact ENNReal.ofReal_le_ofReal_iff (cdf_nonneg _ _)
  have heq : {y : ℝ | ENNReal.ofReal α ≤ P {q | X q ≤ y}} = {y : ℝ | α ≤ F y} := by
    ext y
    exact hf y
  let S := {y : ℝ | α ≤ F y}
  have hne : S.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop (P.map X)).eventually (eventually_gt_nhds hα1)).exists
    exact ⟨y, hy.le⟩
  have hb : BddBelow S := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot (P.map X)).eventually (eventually_lt_nhds hα0)).exists
    refine ⟨y, fun z hz => ?_⟩
    by_contra h
    have hzy : z ≤ y := le_of_not_ge h
    have hh := F.mono hzy
    exact (not_lt_of_ge (hz.trans hh)) hy
  have hmem : α ≤ F (sInf S) := by
    have hlim : Tendsto F (𝓝[>] sInf S) (𝓝 (F (sInf S))) :=
      (F.right_continuous _).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne hy
    exact hz.trans (F.mono hzy.le)
  rw [hf, MultistageStochastic.valueAtRisk, heq]
  exact ⟨fun h => csInf_le hb h, fun h => hmem.trans (F.mono h)⟩

open DRCVRP.RCI
private lemma demand_measurable : Measurable example1Demand := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · change Measurable (fun u : ℝ => if u ∈ Icc (0:ℝ) 0.075 then (2:ℝ) else 1)
    exact Measurable.ite measurableSet_Icc measurable_const measurable_const
  · change Measurable (fun u : ℝ => if u ∈ Icc (0.1:ℝ) 0.175 then (2:ℝ) else 1)
    exact Measurable.ite measurableSet_Icc measurable_const measurable_const
private lemma pstar_probability : IsProbabilityMeasure example1PStar := by
  haveI : IsProbabilityMeasure (volume.restrict (Icc (0:ℝ) 1)) := by
    constructor
    norm_num [Measure.restrict_apply_univ, Real.volume_Icc]
  exact Measure.isProbabilityMeasure_map demand_measurable.aemeasurable
private lemma pstar_event (i : Fin 2) :
    example1PStar {q | q i = 2} = ENNReal.ofReal (0.075 : ℝ) ∧
    example1PStar {q | q i = 1} = ENNReal.ofReal (0.925 : ℝ) := by
  haveI := pstar_probability
  have hm2 : MeasurableSet {q : Fin 2 → ℝ | q i = 2} := measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hm1 : MeasurableSet {q : Fin 2 → ℝ | q i = 1} := measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  fin_cases i
  · change example1PStar {q | q 0 = 2} = _ ∧ example1PStar {q | q 0 = 1} = _
    change MeasurableSet {q : Fin 2 → ℝ | q 0 = 2} at hm2
    change MeasurableSet {q : Fin 2 → ℝ | q 0 = 1} at hm1
    have he2 : example1Demand ⁻¹' {q | q 0 = 2} = Icc (0:ℝ) 0.075 := by
      ext u
      simp [example1Demand]
    have he1 : example1Demand ⁻¹' {q | q 0 = 1} = (Icc (0:ℝ) 0.075)ᶜ := by
      ext u
      simp [example1Demand]
    constructor
    · rw [example1PStar, Measure.map_apply demand_measurable hm2, he2,
        Measure.restrict_apply measurableSet_Icc]
      norm_num [Icc_inter_Icc, Real.volume_Icc]
    · rw [example1PStar, Measure.map_apply demand_measurable hm1, he1,
        Measure.restrict_apply measurableSet_Icc.compl]
      rw [Set.inter_comm]
      change volume (Icc (0:ℝ) 1 \ _) = _
      rw [measure_sdiff (by intro x hx; constructor <;> linarith [hx.1,hx.2]) measurableSet_Icc.nullMeasurableSet (by simp)]
      norm_num [Real.volume_Icc]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 3/40)]
      norm_num
  · change example1PStar {q | q 1 = 2} = _ ∧ example1PStar {q | q 1 = 1} = _
    change MeasurableSet {q : Fin 2 → ℝ | q 1 = 2} at hm2
    change MeasurableSet {q : Fin 2 → ℝ | q 1 = 1} at hm1
    have he2 : example1Demand ⁻¹' {q | q 1 = 2} = Icc (0.1:ℝ) 0.175 := by
      ext u
      simp [example1Demand]
    have he1 : example1Demand ⁻¹' {q | q 1 = 1} = (Icc (0.1:ℝ) 0.175)ᶜ := by
      ext u
      simp [example1Demand]
    constructor
    · rw [example1PStar, Measure.map_apply demand_measurable hm2, he2,
        Measure.restrict_apply measurableSet_Icc]
      norm_num [Icc_inter_Icc, Real.volume_Icc]
    · rw [example1PStar, Measure.map_apply demand_measurable hm1, he1,
        Measure.restrict_apply measurableSet_Icc.compl]
      rw [Set.inter_comm]
      change volume (Icc (0:ℝ) 1 \ _) = _
      rw [measure_sdiff (by intro x hx; constructor <;> linarith [hx.1,hx.2]) measurableSet_Icc.nullMeasurableSet (by simp)]
      norm_num [Real.volume_Icc]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 3/40)]
      norm_num

private lemma pstar_mem : example1PStar ∈ example1AmbiguitySet :=
  ⟨pstar_probability, (pstar_event 0).2, (pstar_event 0).1, (pstar_event 1).2, (pstar_event 1).1⟩
private lemma marginal_mass (P : Measure (Fin 2 → ℝ)) (hP : P ∈ example1AmbiguitySet) (i : Fin 2) :
    P {q | q i = 1} = ENNReal.ofReal (0.925 : ℝ) ∧
    P {q | q i = 2} = ENNReal.ofReal (0.075 : ℝ) := by
  fin_cases i
  · exact ⟨hP.2.1, hP.2.2.1⟩
  · exact ⟨hP.2.2.2.1, hP.2.2.2.2⟩
private lemma marginal_var (P : Measure (Fin 2 → ℝ)) (hP : P ∈ example1AmbiguitySet) (i : Fin 2) :
    MultistageStochastic.valueAtRisk P (fun q => q i) 0.9 = 1 := by
  haveI := hP.1
  have hm : MeasurableSet {q : Fin 2 → ℝ | q i = 1} := measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hiff := var_iff P (fun q => q i) (measurable_pi_apply i) 0.9 (by norm_num) (by norm_num)
  apply le_antisymm
  · apply (hiff 1).mp
    calc
      ENNReal.ofReal (0.9:ℝ) ≤ ENNReal.ofReal (0.925:ℝ) := by norm_num
      _ = P {q | q i = 1} := (marginal_mass P hP i).1.symm
      _ ≤ P {q | q i ≤ 1} := measure_mono (fun q hq => le_of_eq hq)
  · by_contra h
    have hv : MultistageStochastic.valueAtRisk P (fun q => q i) 0.9 < 1 := lt_of_not_ge h
    have hh := (hiff _).mpr le_rfl
    have hsub : {q : Fin 2 → ℝ | q i ≤ MultistageStochastic.valueAtRisk P (fun q => q i) 0.9} ⊆ {q | q i = 1}ᶜ := by
      intro q hq hq1
      change q i = 1 at hq1
      change q i ≤ _ at hq
      linarith
    have hp := hh.trans (measure_mono hsub)
    rw [prob_compl_eq_one_sub hm, (marginal_mass P hP i).1] at hp
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 0.925)] at hp
    have hh := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 1 - 0.925)).mp hp
    norm_num at hh
private lemma marginal_support (P : Measure (Fin 2 → ℝ)) (hP : P ∈ example1AmbiguitySet) (i : Fin 2) :
    ∀ᵐ q ∂P, q i ≤ 2 := by
  haveI := hP.1
  have hm1 : MeasurableSet {q : Fin 2 → ℝ | q i = 1} := measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hm2 : MeasurableSet {q : Fin 2 → ℝ | q i = 2} := measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  have hd : Disjoint {q : Fin 2 → ℝ | q i = 1} {q | q i = 2} := by
    rw [Set.disjoint_left]
    intro q h1 h2
    change q i = 1 at h1
    change q i = 2 at h2
    linarith
  have hu : P ({q | q i = 1} ∪ {q | q i = 2}) = 1 := by
    rw [measure_union hd hm2, (marginal_mass P hP i).1, (marginal_mass P hP i).2]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have ha := (mem_ae_iff_prob_eq_one (hm1.union hm2)).mpr hu
  filter_upwards [ha] with q hq
  rcases hq with hq | hq <;> change q i = _ at hq <;> linarith
private lemma sum_var_upper (P : Measure (Fin 2 → ℝ)) (hP : P ∈ example1AmbiguitySet) :
    MultistageStochastic.valueAtRisk P (fun q => q 0 + q 1) 0.9 ≤ 4 := by
  haveI := hP.1
  apply (var_iff P _ (by fun_prop) 0.9 (by norm_num) (by norm_num) 4).mp
  have ha : ∀ᵐ q ∂P, q 0 + q 1 ≤ 4 := by
    filter_upwards [marginal_support P hP 0, marginal_support P hP 1] with q h0 h1
    linarith
  have hm : MeasurableSet {q : Fin 2 → ℝ | q 0 + q 1 ≤ 4} := by measurability
  rw [(mem_ae_iff_prob_eq_one hm).mp ha]
  norm_num

private lemma pstar_sum_mass : example1PStar {q | q 0 + q 1 = 3} = ENNReal.ofReal (0.15:ℝ) := by
  have he : example1Demand ⁻¹' {q | q 0 + q 1 = 3} = Icc (0:ℝ) 0.075 ∪ Icc (0.1:ℝ) 0.175 := by
    ext u
    change ((if u ∈ Icc (0:ℝ) 0.075 then (2:ℝ) else 1) + (if u ∈ Icc (0.1:ℝ) 0.175 then (2:ℝ) else 1) = 3) ↔ u ∈ Icc (0:ℝ) 0.075 ∪ Icc (0.1:ℝ) 0.175
    by_cases h0 : u ∈ Icc (0:ℝ) 0.075 <;> by_cases h1 : u ∈ Icc (0.1:ℝ) 0.175
    · have := h0.2
      have := h1.1
      linarith
    all_goals simp only [Set.mem_union, h0, h1, ite_true, ite_false]; norm_num
  have hd : Disjoint (Icc (0:ℝ) 0.075) (Icc (0.1:ℝ) 0.175) := by
    rw [Set.disjoint_left]
    intro u h0 h1
    linarith [h0.2,h1.1]
  have hs : Icc (0:ℝ) 0.075 ∪ Icc (0.1:ℝ) 0.175 ⊆ Icc (0:ℝ) 1 := by
    intro u hu
    rcases hu with hu | hu <;> constructor <;> linarith [hu.1,hu.2]
  rw [example1PStar, Measure.map_apply demand_measurable (by measurability), he,
    Measure.restrict_apply (measurableSet_Icc.union measurableSet_Icc),
    inter_eq_self_of_subset_left hs, measure_union hd measurableSet_Icc]
  rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
private lemma pstar_sum_var : MultistageStochastic.valueAtRisk example1PStar (fun q => q 0 + q 1) 0.9 = 3 := by
  haveI := pstar_probability
  have hiff := var_iff example1PStar (fun q => q 0+q 1) (by fun_prop) 0.9 (by norm_num) (by norm_num)
  apply le_antisymm
  · apply (hiff 3).mp
    have he : example1Demand ⁻¹' {q | q 0+q 1 ≤ 3} = univ := by
      ext u
      change ((if u ∈ Icc (0:ℝ) 0.075 then (2:ℝ) else 1) + (if u ∈ Icc (0.1:ℝ) 0.175 then (2:ℝ) else 1) ≤ 3) ↔ True
      by_cases h0 : u ∈ Icc (0:ℝ) 0.075 <;> by_cases h1 : u ∈ Icc (0.1:ℝ) 0.175
      · have := h0.2
        have := h1.1
        linarith
      all_goals simp only [Set.mem_union, h0, h1, ite_true, ite_false]; norm_num
    rw [example1PStar, Measure.map_apply demand_measurable (by measurability), he]
    norm_num [Measure.restrict_apply_univ, Real.volume_Icc]
  · by_contra h
    have hv : MultistageStochastic.valueAtRisk example1PStar (fun q => q 0+q 1) 0.9 < 3 := lt_of_not_ge h
    have hh := (hiff _).mpr le_rfl
    have hm : MeasurableSet {q : Fin 2 → ℝ | q 0+q 1 = 3} := by measurability
    have hs : {q : Fin 2 → ℝ | q 0+q 1 ≤ MultistageStochastic.valueAtRisk example1PStar (fun q => q 0+q 1) 0.9} ⊆ {q | q 0+q 1 = 3}ᶜ := by
      intro q hq hq3
      change q 0+q 1 ≤ _ at hq
      change q 0+q 1 = 3 at hq3
      linarith
    have hp := hh.trans (measure_mono hs)
    rw [prob_compl_eq_one_sub hm, pstar_sum_mass, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 0.15)] at hp
    have hh := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 1-0.15)).mp hp
    norm_num at hh
private lemma worst_singleton (i : Fin 2) : worstCaseVaR example1AmbiguitySet 0.1 {i} = 1 := by
  have he : ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ j ∈ ({i}:Finset (Fin 2)), q j) (1-0.1)) '' example1AmbiguitySet) = {1} := by
    ext x
    constructor
    · rintro ⟨P,hP,rfl⟩
      simp only [Finset.sum_singleton, mem_singleton_iff]
      rw [show (1-(0.1:ℝ))=0.9 by norm_num]
      exact marginal_var P hP i
    · intro hx
      have hx' : x = 1 := hx
      subst x
      refine ⟨example1PStar,pstar_mem,?_⟩
      simpa [show (1-(0.1:ℝ))=0.9 by norm_num] using marginal_var example1PStar pstar_mem i
  unfold worstCaseVaR
  rw [he, csSup_singleton]
private lemma worst_sum_lower : 3 ≤ worstCaseVaR example1AmbiguitySet 0.1 {0,1} := by
  have hb : BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ ({0,1}:Finset (Fin 2)), q i) (1-0.1)) '' example1AmbiguitySet) := by
    refine ⟨4, ?_⟩
    rintro y ⟨P,hP,rfl⟩
    simpa [show (1-(0.1:ℝ))=0.9 by norm_num] using sum_var_upper P hP
  apply le_csSup hb
  refine ⟨example1PStar,pstar_mem,?_⟩
  simpa only [Finset.sum_insert, Finset.sum_singleton, show (0:Fin 2) ∉ ({1}:Finset (Fin 2)) by decide,
    not_false_eq_true, if_true, show (1-(0.1:ℝ))=0.9 by norm_num] using pstar_sum_var

private lemma estimator_lower : (3:ℤ) ≤ demandEstimator example1AmbiguitySet 0.1 1 {0,1} := by
  have hc : (3:ℤ) ≤ ⌈worstCaseVaR example1AmbiguitySet 0.1 {0,1}⌉ := by
    simpa using Int.ceil_mono worst_sum_lower
  simp only [demandEstimator, Finset.insert_ne_empty, ↓reduceIte, div_one]
  exact hc.trans (le_max_left _ _)

theorem solution :
    worstCaseVaR example1AmbiguitySet 0.1 {0} = 1 ∧
    worstCaseVaR example1AmbiguitySet 0.1 {1} = 1 ∧
    3 ≤ worstCaseVaR example1AmbiguitySet 0.1 {0, 1} ∧
    worstCaseVaR example1AmbiguitySet 0.1 {0} + worstCaseVaR example1AmbiguitySet 0.1 {1} <
      worstCaseVaR example1AmbiguitySet 0.1 {0, 1} ∧
    ¬ (demandEstimator example1AmbiguitySet 0.1 1 ({0} ∪ {1}) ≤
        demandEstimator example1AmbiguitySet 0.1 1 {0} +
          demandEstimator example1AmbiguitySet 0.1 1 {1}) := by
  refine ⟨worst_singleton 0,worst_singleton 1,worst_sum_lower,?_,?_⟩
  · rw [worst_singleton, worst_singleton]
    linarith [worst_sum_lower]
  · intro h
    have hl := estimator_lower
    have hsingle (i : Fin 2) : demandEstimator example1AmbiguitySet 0.1 1 {i} = 1 := by
      simp only [demandEstimator, Finset.singleton_ne_empty, ↓reduceIte, div_one, worst_singleton]
      norm_num
    simp only [hsingle,Finset.singleton_union] at h
    omega
