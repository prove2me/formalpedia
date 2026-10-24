-- Prove2me | solution 1 for BOLDSelect.Balance.bold_consistency
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T01:11:56.35569+00:00
-- url     : https://prove2.me/submissions/5ff8765a-5ab7-4d03-86c2-0356637c0e53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_BOLDSelect_Balance_RateFunction
import Definitions.Def_BOLDSelect_Balance_Algorithm
import Definitions.Def_BOLDSelect_Balance_Assumptions
import Theorems.Thm_BOLDSelect_Balance_bold_consistency_pathwise

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open BOLDSelect.Balance

theorem solution
    {M : ℕ} (hM : 2 < M) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fam : Fin M → ℝ → Measure ℝ) (hFam : ∀ x θ, IsProbabilityMeasure (Fam x θ))
    (μ : Fin M → ℝ) (hμ : Function.Injective μ)
    (a b : Fin M → ℝ) (hH : ∀ x, a x < b x ∧ μ x ∈ Set.Ioo (a x) (b x))
    (Θ : Fin M → Set ℝ) (hΘ : ParameterSpace Fam μ Θ a b)
    (hA1 : Assumption1 Fam a b) (hA2 : Assumption2 Fam a b) (hA3 : Assumption3 Fam)
    (W : Fin M → ℕ → Ω → ℝ) (hW : ObsArray P (fun x => Fam x (μ x)) W)
    (θ0 : Fin M → ℝ) (hθ0 : ∀ x, θ0 x ∈ Θ x) (X : ℕ → Ω → Fin M)
    (hX : ∀ ω, IsBOLD Fam θ0 (fun x k => W x k ω) (fun n => X n ω)) :
    ∀ᵐ ω ∂P, ∀ x : Fin M,
      Tendsto (fun n => sampleCount (fun m => X m ω) n x) atTop atTop := by
  have hμΘ : ∀ x, μ x ∈ Θ x := fun x =>
    (hΘ.1 x).2.2.1 ⟨(hH x).2.1.le, (hH x).2.2.le⟩
  -- every sample lies in `Θ x` almost surely
  have hin : ∀ᵐ ω ∂P, ∀ x k, W x k ω ∈ Θ x := by
    rw [ae_all_iff]; intro x; rw [ae_all_iff]; intro k
    have hmeasΘ : MeasurableSet (Θ x)ᶜ := ((hΘ.1 x).1.measurableSet).compl
    have h0 : P (W x k ⁻¹' (Θ x)ᶜ) = 0 := by
      rw [← Measure.map_apply (hW.meas x k) hmeasΘ, hW.law x k]
      exact (hΘ.1 x).2.2.2
    rw [ae_iff]
    simpa [Set.preimage, Set.mem_compl_iff] using h0
  -- the strong law for every alternative
  have hslln : ∀ᵐ ω ∂P, ∀ x, Tendsto (fun k : ℕ => (∑ j ∈ Finset.range k, W x j ω) / (k : ℝ))
      atTop (𝓝 (μ x)) := by
    rw [ae_all_iff]; intro x
    have hint : Integrable (W x 0) P := by
      have h1 : Integrable id (P.map (W x 0)) := by
        rw [hW.law x 0]; exact ((hΘ.2.1 x (μ x) (hμΘ x)).1)
      exact (integrable_map_measure aestronglyMeasurable_id
        (hW.meas x 0).aemeasurable).1 h1
    have hindep : Pairwise (Function.onFun (fun f g => IndepFun f g P) (fun k => W x k)) := by
      intro i j hij
      have := hW.indep.indepFun (i := (x, i)) (j := (x, j)) (by simpa using hij)
      exact this
    have hident : ∀ i, IdentDistrib (W x i) (W x 0) P P := fun i =>
      { aemeasurable_fst := (hW.meas x i).aemeasurable
        aemeasurable_snd := (hW.meas x 0).aemeasurable
        map_eq := by rw [hW.law x i, hW.law x 0] }
    have hmean : P[W x 0] = μ x := by
      have : ∫ ω, W x 0 ω ∂P = ∫ t, t ∂(P.map (W x 0)) := by
        exact (integral_map (f := fun t : ℝ => t) (hW.meas x 0).aemeasurable
          aestronglyMeasurable_id).symm
      rw [this, hW.law x 0]
      exact (hΘ.2.1 x (μ x) (hμΘ x)).2
    filter_upwards [strong_law_ae (fun k => W x k) hint hindep hident] with ω hω
    rw [hmean] at hω
    refine hω.congr (fun k => ?_)
    simp [smul_eq_mul, div_eq_inv_mul]
  filter_upwards [hin, hslln] with ω h1 h2
  exact bold_consistency_pathwise hM Fam hFam μ hμ a b hH Θ hΘ hA1 hA2 hA3
    (fun x k => W x k ω) h1 h2 θ0 hθ0 (fun n => X n ω) (hX ω)
