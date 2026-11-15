-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a432_discrete_Banach_martingale_Doob_Lp_maximal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:57:57.962458+00:00
-- url     : https://prove2.me/submissions/da5e03a3-2910-4f80-9c3e-53259b7744f9

import Mathlib
import Theorems.Thm_MeasureTheory_maximal_ineq_Lp_readable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory ENNReal Filter Set Finset MeasureTheory
open scoped NNReal ENNReal
noncomputable section

private lemma norm_sample_submartingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ mΩ} {f : ℕ → Ω → E} (hf : Martingale f 𝒢 μ) :
    Submartingale (fun n ω => ‖f n ω‖) 𝒢 μ := by
  refine ⟨fun n => continuous_norm.comp_stronglyMeasurable (hf.stronglyAdapted n),
          fun i j hij => ?_, fun n => (hf.integrable n).norm⟩
  have hcondExp : f i =ᵐ[μ] μ[f j | (𝒢 i : MeasurableSpace Ω)] :=
    (hf.condExp_ae_eq hij).symm
  filter_upwards [hcondExp,
    norm_condExp_le (f := f j) (m := (𝒢 i : MeasurableSpace Ω)) (μ := μ)]
    with ω hω hjensen
  calc
    ‖f i ω‖ = ‖(μ[f j | (𝒢 i : MeasurableSpace Ω)]) ω‖ := by rw [hω]
    _ ≤ _ := hjensen

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ mΩ} {f : ℕ → Ω → E} {p : ℝ}
    (hf : Martingale f 𝒢 μ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω => (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k => ‖f k ω‖))
      (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hsub := norm_sample_submartingale hf
  have hbound := maximal_ineq_Lp_readable hsub
    (fun _ _ => norm_nonneg _) hp n
  rwa [eLpNorm_norm] at hbound
