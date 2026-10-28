-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.exists_le_setIntegral_div_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:50.83704+00:00
-- url     : https://prove2.me/submissions/c805b533-84e6-494a-9c9d-d0f48aa9ab76

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary

noncomputable section
section S7B2BoundaryMeanValue
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
 theorem solution
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Integrable f (volume.restrict (Set.Ioc T (2 * T)))) :
    ∃ t ∈ Set.Icc T (2 * T),
      f t ≤ (∫ s in Set.Ioc T (2 * T), f s) / T := by
  let S : Set ℝ := Set.Ioc T (2 * T)
  let ν : Measure ℝ := volume.restrict S
  let A : ℝ := (∫ s in S, f s) / T
  by_contra hn
  have hn' : ∀ t ∈ Set.Icc T (2 * T), A < f t := by
    intro t ht
    have hnot : ¬ f t ≤ A := by
      intro hle
      exact hn ⟨t, ht, hle⟩
    exact lt_of_not_ge hnot
  have hnonneg : 0 ≤ᵐ[ν] fun s => f s - A := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact sub_nonneg.mpr (le_of_lt (hn' s hs'))
  have hfi : Integrable (fun s => f s - A) ν := by
    apply hf.sub
    exact integrable_const A
  have hsupport : S ⊆ Function.support (fun s => f s - A) := by
    intro s hs
    have hs' : s ∈ Set.Icc T (2 * T) := ⟨hs.1.le, hs.2⟩
    exact ne_of_gt (sub_pos.mpr (hn' s hs'))
  have hνS : 0 < ν S := by
    dsimp [ν, S]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_self, Real.volume_Ioc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hpos : 0 < ∫ s, f s - A ∂ν := by
    apply (integral_pos_iff_support_of_nonneg_ae hnonneg hfi).2
    exact lt_of_lt_of_le hνS (measure_mono hsupport)
  have hmeasure : ν.real Set.univ = T := by
    dsimp [ν, S]
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hsub :
      (∫ s in S, f s) - A * T = ∫ s, f s - A ∂ν := by
    rw [integral_sub hf (integrable_const A), integral_const]
    simp only [smul_eq_mul]
    rw [hmeasure]
    ring
  have hzero : (∫ s in S, f s) - A * T = 0 := by
    dsimp [A]
    field_simp [ne_of_gt hT]; ring
  linarith
