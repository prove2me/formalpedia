-- Prove2me | solution 1 for AzumaWeightedSums.Multiplicative.lemma1_mgf_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:43:36.380407+00:00
-- url     : https://prove2.me/submissions/00c29edf-6e85-4fe2-b975-1ee4f285755a

import Mathlib
import Definitions.Def_AzumaWeightedSums_Multiplicative_IsMultiplicativeSystem

set_option autoImplicit false

namespace AzumaLemma1Aux

open MeasureTheory AzumaWeightedSums.Multiplicative

lemma exp_mul_le_cosh_add {c y : ℝ} (hy : |y| ≤ 1) :
    Real.exp (c * y) ≤ y * Real.sinh c + Real.cosh c := by
  have hyl : -1 ≤ y := (abs_le.mp hy).1
  have hyu : y ≤ 1 := (abs_le.mp hy).2
  have key : c * y = ((1 + y) / 2) * c + ((1 - y) / 2) * (-c) := by ring
  have hc := convexOn_exp.2 (Set.mem_univ c) (Set.mem_univ (-c))
    (show (0:ℝ) ≤ (1 + y) / 2 by linarith) (show (0:ℝ) ≤ (1 - y) / 2 by linarith)
    (by ring)
  simp only [smul_eq_mul] at hc
  rw [key]
  refine hc.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

lemma abs_sinh_cosh_le {c y : ℝ} (hy : |y| ≤ 1) :
    |y * Real.sinh c + Real.cosh c| ≤ Real.cosh c + |Real.sinh c| := by
  calc |y * Real.sinh c + Real.cosh c| ≤ |y * Real.sinh c| + |Real.cosh c| := abs_add_le _ _
    _ ≤ Real.cosh c + |Real.sinh c| := by
        rw [abs_of_pos (Real.cosh_pos c), abs_mul]
        have : |y| * |Real.sinh c| ≤ 1 * |Real.sinh c| :=
          mul_le_mul_of_nonneg_right hy (abs_nonneg _)
        linarith

lemma ae_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) :
    ∀ᵐ ω ∂μ, ∀ n, 1 ≤ n → |x n ω| ≤ 1 := by
  rw [ae_all_iff]; intro n
  by_cases hn : 1 ≤ n
  · filter_upwards [hM.2.1 n hn] with ω h _ using h
  · exact Filter.Eventually.of_forall (fun ω h => absurd h hn)

lemma integrable_prod_x {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (t : Finset ℕ) (ht : ∀ i ∈ t, 1 ≤ i) :
    Integrable (fun ω => ∏ i ∈ t, x i ω) μ := by
  have hmeas : Measurable (fun ω => ∏ i ∈ t, x i ω) :=
    Finset.measurable_prod t (fun i hi => hM.1 i (ht i hi))
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
  filter_upwards [ae_bound hM] with ω hω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i hi => hω i (ht i hi))

lemma integral_prod_cosh {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (I : Finset ℕ) (hI : ∀ i ∈ I, 1 ≤ i)
    (c : ℕ → ℝ) :
    ∫ ω, ∏ i ∈ I, (x i ω * Real.sinh (c i) + Real.cosh (c i)) ∂μ = ∏ i ∈ I, Real.cosh (c i) := by
  simp_rw [Finset.prod_add, Finset.prod_mul_distrib]
  rw [integral_finset_sum]
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro t ht hne
      rw [integral_mul_const, integral_mul_const,
        hM.2.2 t (Finset.nonempty_iff_ne_empty.2 hne)
          (fun i hi => hI i (Finset.mem_powerset.1 ht hi))]
      simp
    · intro h; exact absurd (Finset.empty_mem_powerset I) h
  · intro t ht
    exact ((integrable_prod_x hM t (fun i hi => hI i (Finset.mem_powerset.1 ht hi))).mul_const
      _).mul_const _

lemma mgf_bound' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {x : ℕ → Ω → ℝ} (hM : IsMultiplicativeSystem μ x) (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∫ ω, Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω) ∂μ ≤
      Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, (b k) ^ 2) := by
  have hI : ∀ i ∈ Finset.Icc 1 n, 1 ≤ i := fun i hi => (Finset.mem_Icc.1 hi).1
  set c : ℕ → ℝ := fun k => t * b k with hc
  set g : Ω → ℝ := fun ω => ∏ i ∈ Finset.Icc 1 n, (x i ω * Real.sinh (c i) + Real.cosh (c i))
    with hg
  have hpt : ∀ᵐ ω ∂μ, Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω) ≤ g ω := by
    filter_upwards [ae_bound hM] with ω hω
    have : t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω = ∑ i ∈ Finset.Icc 1 n, c i * x i ω := by
      simp only [Finset.mul_sum, hc]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [this, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      (fun i hi => exp_mul_le_cosh_add (hω i (hI i hi)))
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ (fun i hi => ((hM.1 i (hI i hi)).mul_const _).add_const _)
  have hg_int : Integrable g μ := by
    refine Integrable.of_bound hg_meas.aestronglyMeasurable
      (∏ i ∈ Finset.Icc 1 n, (Real.cosh (c i) + |Real.sinh (c i)|)) ?_
    filter_upwards [ae_bound hM] with ω hω
    rw [Real.norm_eq_abs, Finset.abs_prod]
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
      (fun i hi => abs_sinh_cosh_le (hω i (hI i hi)))
  have hsum_meas : Measurable (fun ω => ∑ k ∈ Finset.Icc 1 n, b k * x k ω) :=
    Finset.measurable_sum _ (fun k hk => (hM.1 k (Finset.mem_Icc.1 hk).1).const_mul _)
  have hmeas : Measurable (fun ω => Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hsum_meas)
  have hlhs : Integrable (fun ω => Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω)) μ := by
    refine Integrable.mono' hg_int hmeas.aestronglyMeasurable ?_
    filter_upwards [hpt] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact h
  calc ∫ ω, Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω) ∂μ ≤ ∫ ω, g ω ∂μ :=
        integral_mono_ae hlhs hg_int hpt
    _ = ∏ i ∈ Finset.Icc 1 n, Real.cosh (c i) := integral_prod_cosh hM _ hI c
    _ ≤ ∏ i ∈ Finset.Icc 1 n, Real.exp (c i ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => (Real.cosh_pos _).le)
          (fun i _ => Real.cosh_le_exp_half_sq _)
    _ = Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, (b k) ^ 2) := by
        rw [← Real.exp_sum, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [hc]
        ring

end AzumaLemma1Aux

open MeasureTheory AzumaWeightedSums.Multiplicative in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℕ → Ω → ℝ) (hM : IsMultiplicativeSystem μ x)
    (n : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ∫ ω, Real.exp (t * ∑ k ∈ Finset.Icc 1 n, b k * x k ω) ∂μ ≤
      Real.exp ((t ^ 2 / 2) * ∑ k ∈ Finset.Icc 1 n, (b k) ^ 2) := by
  exact AzumaLemma1Aux.mgf_bound' hM n b t
