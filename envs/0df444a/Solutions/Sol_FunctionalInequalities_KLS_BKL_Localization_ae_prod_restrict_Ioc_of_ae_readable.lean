-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.ae_prod_restrict_Ioc_of_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:21:04.942046+00:00
-- url     : https://prove2.me/submissions/61b677a3-a901-4e10-a1c1-10cbe8697549

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
omit [IsProbabilityMeasure P] in
/-- Almost-sure statements valid for all `s ≥ 0` transfer to the product measure
`P ⊗ Leb|_{(0,T]}`. -/
theorem solution
    [IsProbabilityMeasure P]
    {Q : Ω → ℝ → Prop}
    (hQ : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) (T : ℝ) :
    ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))), Q z.1 z.2 := by
  rw [ae_iff] at hQ ⊢
  apply measure_mono_null
    (t := {w | ¬ ∀ s : ℝ, 0 ≤ s → Q w s} ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ)
  · intro z hz
    by_cases hS : ∀ s : ℝ, 0 ≤ s → Q z.1 s
    · right
      refine ⟨Set.mem_univ _, fun hs => ?_⟩
      exact hz (hS z.2 hs.1.le)
    · left
      exact ⟨hS, Set.mem_univ _⟩
  · apply measure_union_null
    · rw [Measure.prod_prod, hQ, zero_mul]
    · rw [Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl,
        Set.compl_inter_self, measure_empty, mul_zero]
