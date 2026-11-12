-- Prove2me | solution 1 for DistributionFreeInventory.TwoLocation.theorem_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:56:30.763203+00:00
-- url     : https://prove2.me/submissions/3456655b-c3ec-4e99-ba30-2e8e716e8be4

import Definitions.Def_DistributionFreeInventory_TwoLocation_Bounds

open MeasureTheory
open scoped BigOperators ENNReal

namespace DistributionFreeInventory.TwoLocation

private noncomputable def ceMean : Demand := WithLp.toLp 2 (fun _ => (1 : ℝ))

private noncomputable def ceMoments : Moments where
  mean := ceMean
  sigma := fun _ => 2
  rho := 0
  sigma_nonneg := by
    intro _
    norm_num
  rho_lower := by norm_num
  rho_upper := by norm_num

private noncomputable def cePts (k : Fin 4) : Demand :=
  WithLp.toLp 2 (fun i =>
    if i = 0 then (if k = 0 ∨ k = 1 then -1 else 3)
    else (if k = 0 ∨ k = 2 then -1 else 3))

private noncomputable def ceLaw : Measure Demand :=
  ∑ k : Fin 4, ENNReal.ofReal (1 / 4 : ℝ) • Measure.dirac (cePts k)

private lemma ceLaw_prob : IsProbabilityMeasure ceLaw := by
  constructor
  simp only [ceLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [Fin.sum_univ_four,
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private lemma integral_ceLaw {g : Demand → ℝ} :
    ∫ R, g R ∂ceLaw = (1 / 4 : ℝ) * (g (cePts 0) + g (cePts 1) + g (cePts 2) + g (cePts 3)) := by
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin 4)),
      Integrable g (ENNReal.ofReal (1 / 4 : ℝ) • Measure.dirac (cePts k)) := by
    intro k _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  rw [ceLaw, integral_finsetSum_measure hint]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4), Fin.sum_univ_four]
  ring

private lemma ceLaw_mem_ambiguity : ceLaw ∈ ambiguity ceMoments := by
  have : IsProbabilityMeasure ceLaw := ceLaw_prob
  refine ⟨ceLaw_prob, ?_, ?_, ?_⟩
  · intro i
    have hcont : Continuous (fun R : Demand => R i) := EuclideanSpace.proj i |>.continuous
    refine MemLp.of_bound hcont.aestronglyMeasurable 3 ?_
    rw [ae_iff]
    have hmeas : MeasurableSet {R : Demand | ¬ ‖R i‖ ≤ 3} :=
      (isClosed_le (continuous_norm.comp hcont) continuous_const).measurableSet.compl
    simp only [ceLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Measure.dirac_apply' _ hmeas]
    have hle : |(cePts k) i| ≤ 3 := by
      fin_cases k <;> fin_cases i <;> simp [cePts]
    simp [Set.indicator, hle]
  · intro i
    rw [integral_ceLaw]
    fin_cases i <;> simp [cePts, ceMoments, ceMean] <;> norm_num
  · intro i j
    rw [integral_ceLaw]
    fin_cases i <;> fin_cases j <;> simp [cePts, ceMoments, ceMean, covariance] <;> norm_num

private lemma recourse_cePts0_eq_top :
    recourse 1 3 (twoMatrix 1 2) (fun i => ceMean i) (fun i => cePts 0 i) = ⊤ := by
  unfold recourse
  rw [eq_top_iff]
  refine le_iInf fun z => le_iInf fun hz => False.elim ?_
  have h00 : 0 ≤ z 0 0 := hz.1 0 0
  have h10 : 0 ≤ z 1 0 := hz.1 1 0
  have hd0 : ∑ i : Fin 2, z i 0 ≤ cePts 0 0 := hz.2.2 0
  rw [Fin.sum_univ_two] at hd0
  have hpt : cePts 0 0 = -1 := by simp [cePts]
  linarith

private lemma expectedCost_ceLaw_eq_top :
    expectedCost 1 3 1 2 ceMean ceLaw = ⊤ := by
  unfold expectedCost
  suffices hlint :
      (∫⁻ d, recourse 1 3 (twoMatrix 1 2) (fun i => ceMean i) (fun i => d i) ∂ceLaw) = ⊤ by
    rw [hlint]
    rfl
  rw [eq_top_iff]
  have hsing_le :
      ∫⁻ d, ({cePts 0} : Set Demand).indicator (fun _ => (⊤ : ℝ≥0∞)) d ∂ceLaw ≤
        ∫⁻ d, recourse 1 3 (twoMatrix 1 2) (fun i => ceMean i) (fun i => d i) ∂ceLaw := by
    refine lintegral_mono fun d => ?_
    by_cases hd : d = cePts 0
    · subst hd
      simp [recourse_cePts0_eq_top]
    · simp [hd]
  rw [lintegral_indicator (measurableSet_singleton (cePts 0)), lintegral_const,
    Measure.restrict_apply_univ] at hsing_le
  have hmass : ENNReal.ofReal (1 / 4 : ℝ) ≤ ceLaw {cePts 0} := by
    simp only [ceLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ (0 : Fin 4)))
    simp
  have hpos : ceLaw {cePts 0} ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hmass)
  rw [ENNReal.top_mul hpos] at hsing_le
  exact hsing_le

end DistributionFreeInventory.TwoLocation

open DistributionFreeInventory.TwoLocation in
theorem solution : ¬ (∀ (M : Moments) (h p s0 s : ℝ)
    (_hh : 0 < h) (_hp : 0 < p) (_hs0 : 0 < s0) (_hs : s0 < s) (_hph : s < p+h)
    (y : Demand),
    worstCost M h p s0 s y ≤ (costBound M h p s0 s y : EReal) ∧
    (conditionOne M y ((p+h-s)/(s-s0)) →
      ∃ μ ∈ ambiguity M, SixPointLaw μ ∧
        expectedCost h p s0 s y μ = (costBound M h p s0 s y : EReal))) := by
  intro hall
  have h1 := (hall ceMoments 1 3 1 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ceMean).1
  have htop : (⊤ : EReal) ≤ worstCost ceMoments 1 3 1 2 ceMean := by
    unfold worstCost
    rw [← expectedCost_ceLaw_eq_top]
    exact le_iSup₂_of_le ceLaw ceLaw_mem_ambiguity le_rfl
  have hle : (⊤ : EReal) ≤ (costBound ceMoments 1 3 1 2 ceMean : EReal) := htop.trans h1
  exact EReal.coe_ne_top _ (top_unique hle)
