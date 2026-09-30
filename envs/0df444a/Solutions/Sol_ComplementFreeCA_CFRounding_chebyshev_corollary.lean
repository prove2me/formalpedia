-- Prove2me | solution 1 for ComplementFreeCA.CFRounding.chebyshev_corollary
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:13:06.706972+00:00
-- url     : https://prove2.me/submissions/14995b29-63e1-4edd-bac6-170ee222d354

import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {N : ℕ} (X : Fin N → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hrange : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) (hα : 0 < α) :
    μ.real {ω | α ≤ |∑ i, X i ω - ∫ ω', ∑ i, X i ω' ∂μ|} ≤ (∫ ω', ∑ i, X i ω' ∂μ) / α ^ 2 := by
  have hLp : ∀ i, MemLp (X i) 2 μ := fun i => memLp_of_bounded
    (Filter.Eventually.of_forall (hrange i)) (hmeas i).aestronglyMeasurable 2
  have hInt : ∀ i, Integrable (X i) μ := fun i => (hLp i).integrable (by norm_num)
  have hsLp : MemLp (fun ω => ∑ i, X i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i hi => hLp i)
  have hvar : variance (fun ω => ∑ i, X i ω) μ ≤ ∫ ω, ∑ i, X i ω ∂μ := by
    have he : variance (fun ω => ∑ i, X i ω) μ = ∑ i, variance (X i) μ := by
      have hf : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
        funext ω
        simp
      rw [hf]
      exact IndepFun.variance_sum (s := Finset.univ) (fun i hi => hLp i)
        (fun i hi i' hi' hne => hind.indepFun hne)
    rw [he, integral_finsetSum Finset.univ (fun i hi => hInt i)]
    apply Finset.sum_le_sum
    intro i hi
    rw [variance_eq_sub (hLp i)]
    have hsq : (∫ ω, (X i ω)^2 ∂μ) ≤ ∫ ω, X i ω ∂μ :=
      integral_mono (hLp i).integrable_sq (hInt i) (fun ω => by
        obtain ⟨h0,h1⟩ := hrange i ω
        nlinarith)
    change (∫ ω, (X i ω)^2 ∂μ) - (∫ ω, X i ω ∂μ)^2 ≤ ∫ ω, X i ω ∂μ
    nlinarith [sq_nonneg (∫ ω, X i ω ∂μ)]
  have hc := meas_ge_le_variance_div_sq hsLp hα
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ μ) (sq_nonneg α))] at hr
  exact hr.trans (div_le_div_of_nonneg_right hvar (sq_nonneg α))
