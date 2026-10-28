-- Prove2me | solution 1 for ForecastComp.IELF.hoeffding_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:19:09.702426+00:00
-- url     : https://prove2.me/submissions/1cb2438a-648e-4932-9e6a-f982977261e1

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

open MeasureTheory ProbabilityTheory

private theorem hoeff_aux {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, X k ω ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ k, X k ω) - ∫ ω', (∑ k, X k ω') ∂μ} ≤
        Real.exp (-2 * t ^ 2 / (m:ℝ)) := by
  have hint : ∀ k, Integrable (X k) μ := fun k =>
    Integrable.of_mem_Icc 0 1 (hmeas k).aemeasurable (hbd k)
  have hsub : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => X k ω - μ[X k]) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) μ :=
    fun k _ => hasSubgaussianMGF_of_mem_Icc (hmeas k).aemeasurable (hbd k)
  have hind' : iIndepFun (fun k ω => X k ω - μ[X k]) μ :=
    hind.comp (g := fun k (x : ℝ) => x - ∫ ω, X k ω ∂μ) (fun k => measurable_id.sub_const _)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub ht
  have hsum : ∀ ω, ∑ k, (X k ω - μ[X k]) = (∑ k, X k ω) - ∫ ω', (∑ k, X k ω') ∂μ := by
    intro ω
    rw [integral_finsetSum _ (fun k _ => hint k), Finset.sum_sub_distrib]
  simp only [hsum] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_zero,
    nnnorm_one, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_mul, NNReal.coe_natCast]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have : (m:ℝ) ≠ 0 := by positivity
    field_simp

theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ k, Measurable (X k)) (hbd : ∀ k, ∀ᵐ ω ∂μ, X k ω ∈ Set.Icc (0:ℝ) 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (∑ k, X k ω) - ∫ ω', (∑ k, X k ω') ∂μ} ≤
        Real.exp (-2 * t ^ 2 / (m:ℝ)) ∧
    μ.real {ω | t ≤ (∫ ω', (∑ k, X k ω') ∂μ) - ∑ k, X k ω} ≤
        Real.exp (-2 * t ^ 2 / (m:ℝ)) := by
  refine ⟨hoeff_aux X hind hmeas hbd t ht, ?_⟩
  have hint : ∀ k, Integrable (X k) μ := fun k =>
    Integrable.of_mem_Icc 0 1 (hmeas k).aemeasurable (hbd k)
  have h := hoeff_aux (fun k ω => 1 - X k ω)
    (hind.comp (fun k x => 1 - x) (fun k => measurable_const.sub measurable_id))
    (fun k => measurable_const.sub (hmeas k))
    (fun k => by
      filter_upwards [hbd k] with ω hω
      exact ⟨by linarith [hω.2], by linarith [hω.1]⟩) t ht
  have e1 : ∀ ω, (∑ k, (1 - X k ω)) = m - ∑ k, X k ω := by
    intro ω; simp
  have e2 : ∫ ω', (m - ∑ k, X k ω') ∂μ = m - ∫ ω', (∑ k, X k ω') ∂μ := by
    rw [integral_sub (integrable_const _) (integrable_finsetSum _ (fun k _ => hint k))]
    simp
  simp only [e1] at h
  rw [e2] at h
  have hs : {ω | t ≤ (∫ ω', (∑ k, X k ω') ∂μ) - ∑ k, X k ω} =
      {ω | t ≤ ((m:ℝ) - ∑ k, X k ω) - ((m:ℝ) - ∫ ω', (∑ k, X k ω') ∂μ)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hs]
  exact h
