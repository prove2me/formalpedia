-- Prove2me | solution 1 for GenEmpLik.Consistency.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:14:01.578388+00:00
-- url     : https://prove2.me/submissions/cadb21a9-788e-4cc2-8c2d-552e1021d8cc

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_uncertaintySet
import Definitions.Def_GenEmpLik_Coverage_AssumptionA
import Definitions.Def_GenEmpLik_Consistency_AssumptionE
import Definitions.Def_GenEmpLik_Consistency_IsGlivenkoCantelli
import Theorems.Thm_GenEmpLik_Consistency_lemma_13
import Theorems.Thm_GenEmpLik_Consistency_eq_47
import Theorems.Thm_GenEmpLik_Consistency_display_after_47

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

theorem solution {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MetricSpace Ξ]
    [SecondCountableTopology Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {d : ℕ}
    (f : ℝ → EReal) (hf : GenEmpLik.Coverage.AssumptionA f) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (ξ : ℕ → Ω → Ξ) (hξm : ∀ i, Measurable (ξ i)) (hξind : iIndepFun ξ μ)
    (hξid : ∀ i, IdentDistrib (ξ i) (ξ 0) μ μ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXne : X.Nonempty) (hXclosed : IsClosed X)
    (ℓ : EuclideanSpace ℝ (Fin d) → Ξ → ℝ)
    (hℓlsc : LowerSemicontinuous (fun xs : X × Ξ => ℓ xs.1 xs.2))
    (hℓm : ∀ x ∈ X, Measurable (ℓ x))
    (hE : GenEmpLik.Consistency.AssumptionE (μ.map (ξ 0)) X ℓ)
    (hGC : GenEmpLik.Consistency.IsGlivenkoCantelli μ ξ ((fun x => ℓ x) '' X)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ⨆ x ∈ X,
        ⨆ p ∈ PhiDivRobust.Counterpart.probUncertaintySet f (fun _ : Fin n => (1 : ℝ) / n)
          (ρ / n),
        ENNReal.ofReal |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))|)
      atTop (𝓝 0) := by
  have : IsProbabilityMeasure (μ.map (ξ 0)) := Measure.isProbabilityMeasure_map (hξm 0).aemeasurable
  obtain ⟨Z, hZm, hZ0, hZb, ε, hε, hZint⟩ := hE
  obtain ⟨cf, Cf, -, -, hCf, -⟩ := GenEmpLik.Consistency.lemma_13 f hf ρ hρ
  have hr2 : (2 : ℝ) ≤ max 2 (1 + 1 / ε) := le_max_left _ _
  have hr0 : (0 : ℝ) < max 2 (1 + 1 / ε) := by linarith
  have hq0 : (0 : ℝ) < min 2 (1 + ε) := lt_min (by norm_num) (by linarith)
  have hq1 : min 2 (1 + ε) ≤ 1 + ε := min_le_right _ _
  set r := max 2 (1 + 1 / ε) with hr
  set q := min 2 (1 + ε) with hq
  have hZqm : Measurable (fun s => Z s ^ q) := hZm.pow_const q
  have hZq : Integrable (fun s => Z s ^ q) (μ.map (ξ 0)) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hZint) hZqm.aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hZ0 s) _)]
    simp only [Pi.add_apply]
    rcases le_total (Z s) 1 with h | h
    · have := Real.rpow_le_one (hZ0 s) h hq0.le
      have := Real.rpow_nonneg (hZ0 s) (1 + ε); linarith
    · have := Real.rpow_le_rpow_of_exponent_le h hq1; linarith
  set Y : ℕ → Ω → ℝ := fun i ω => Z (ξ i ω) ^ q with hY
  have hYint : Integrable (Y 0) μ :=
    (integrable_map_measure hZq.aestronglyMeasurable (hξm 0).aemeasurable).1 hZq
  have hS := strong_law_ae Y hYint
    (fun i j hij => (hξind.comp (fun _ s => Z s ^ q) (fun _ => hZqm)).indepFun hij)
    (fun i => (hξid i).comp hZqm)
  filter_upwards [hS, hGC.2] with ω h1 h2
  set avg : ℕ → ℝ := fun n => (1 / (n : ℝ)) * ∑ i : Fin n, Y i ω with havg
  have havgT : Tendsto avg atTop (𝓝 (μ[Y 0])) := by
    refine h1.congr (fun n => ?_)
    simp only [havg, smul_eq_mul, one_div]
    rw [Fin.sum_univ_eq_sum_range (fun i => Y i ω) n]
  set a : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf) * avg n ^ (1 / q) with ha
  have haT : Tendsto a atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    have hb : Tendsto (fun n => avg n ^ (1 / q)) atTop (𝓝 ((μ[Y 0]) ^ (1 / q))) :=
      havgT.rpow_const (Or.inr (by positivity))
    have h := (hn.mul_const (Real.sqrt (ρ * Cf))).mul hb
    rw [zero_mul, zero_mul] at h
    exact h
  have hsum : Tendsto (fun n => ENNReal.ofReal (a n) + ⨆ h ∈ (fun x => ℓ x) '' X,
      ENNReal.ofReal |VarianceRegularization.Expansion.empMean (fun i : Fin n => h (ξ i ω))
        - ∫ s, h s ∂(μ.map (ξ 0))|) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal haT).add h2
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨1, fun n hn1 => ?_⟩)
  have hn : 0 < n := hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine iSup₂_le fun x hx => iSup₂_le fun p hp => ?_
  have e47 := GenEmpLik.Consistency.eq_47 f ρ ε hε n hn (fun i => ℓ x (ξ i ω))
    (∫ s, ℓ x s ∂(μ.map (ξ 0))) p hp
  have d47 := GenEmpLik.Consistency.display_after_47 f ρ n hn r hr2 Cf (hCf n hn) p hp
  have hA : ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * p i - 1| ^ r) ^ (1 / r) ≤
      (n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf) := by
    rw [d47.1]; exact d47.2.1.trans d47.2.2
  have hB : ((1 / (n : ℝ)) * ∑ i : Fin n, |ℓ x (ξ i ω)| ^ q) ^ (1 / q) ≤ avg n ^ (1 / q) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum; intro i _
    exact Real.rpow_le_rpow (abs_nonneg _) (hZb x hx _) hq0.le
  have hAnn : 0 ≤ ((1 / (n : ℝ)) * ∑ i, |(n : ℝ) * p i - 1| ^ r) ^ (1 / r) :=
    Real.rpow_nonneg (by positivity) _
  have hBnn : 0 ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, |ℓ x (ξ i ω)| ^ q) ^ (1 / q) :=
    Real.rpow_nonneg (by positivity) _
  have hann : 0 ≤ a n := by
    have : 0 ≤ avg n := by
      simp only [havg, hY]; exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hZ0 _) _)
    simp only [ha]; positivity
  have hmain : |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))| ≤ a n +
      |VarianceRegularization.Expansion.empMean (fun i : Fin n => ℓ x (ξ i ω))
        - ∫ s, ℓ x s ∂(μ.map (ξ 0))| := by
    refine (e47.1.trans e47.2).trans ?_
    gcongr
    calc _ ≤ ((n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf)) *
          ((1 / (n : ℝ)) * ∑ i : Fin n, |ℓ x (ξ i ω)| ^ q) ^ (1 / q) := mul_le_mul_of_nonneg_right hA hBnn
      _ ≤ ((n : ℝ) ^ (-(1 / r)) * Real.sqrt (ρ * Cf)) * avg n ^ (1 / q) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
  calc ENNReal.ofReal |∑ i, p i * ℓ x (ξ i ω) - ∫ s, ℓ x s ∂(μ.map (ξ 0))|
      ≤ ENNReal.ofReal (a n + |VarianceRegularization.Expansion.empMean
          (fun i : Fin n => ℓ x (ξ i ω)) - ∫ s, ℓ x s ∂(μ.map (ξ 0))|) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (a n) + ENNReal.ofReal |VarianceRegularization.Expansion.empMean
          (fun i : Fin n => ℓ x (ξ i ω)) - ∫ s, ℓ x s ∂(μ.map (ξ 0))| :=
        ENNReal.ofReal_add hann (abs_nonneg _)
    _ ≤ _ := by
      gcongr
      exact le_iSup₂ (f := fun (h : Ξ → ℝ) (_ : h ∈ (fun x => ℓ x) '' X) => ENNReal.ofReal
        |VarianceRegularization.Expansion.empMean (fun i : Fin n => h (ξ i ω))
          - ∫ s, h s ∂(μ.map (ξ 0))|) (ℓ x) ⟨x, hx, rfl⟩
