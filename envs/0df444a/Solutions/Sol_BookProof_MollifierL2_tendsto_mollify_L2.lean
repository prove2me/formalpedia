-- Prove2me | solution 1 for BookProof.MollifierL2.tendsto_mollify_L2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:07:07.203794+00:00
-- url     : https://prove2.me/submissions/b5804f85-f5ab-49a6-8414-02bb0acaab9c

-- Generated from ChapterMollifierL2.lean — solution of BookProof.MollifierL2.tendsto_mollify_L2
import Mathlib
import Definitions.Def_ChapterMollifierL2
import Theorems.Thm_BookProof_MollifierL2_tendsto_translate_Lp
import Theorems.Thm_BookProof_MollifierL2_eLpNorm_mollify_sub_le
open BookProof.MollifierL2




open MeasureTheory Filter ENNReal Pointwise
open scoped NNReal Topology

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} {l : Filter ι} (u : E → ℂ) (hu : StronglyMeasurable u)
    (hu2 : MemLp u 2 μ) (ρ : ι → E → ℝ) (r : ι → ℝ)
    (hρ0 : ∀ i y, 0 ≤ ρ i y) (hρm : ∀ i, Measurable (ρ i))
    (hρ1 : ∀ i, ∫⁻ y, ENNReal.ofReal (ρ i y) ∂μ = 1)
    (hsupp : ∀ i, ∀ y : E, ρ i y ≠ 0 → ‖y‖ < r i) (hr : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun x => ∫ y, ρ i y • (u (x - y) - u x) ∂μ) 2 μ) l (𝓝 0) := by

  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have htr := tendsto_translate_Lp (μ := μ) (p := 2) (by norm_num) (by norm_num) (by norm_num) hu2
  rw [ENNReal.tendsto_nhds_zero] at htr
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp (htr ε hε)
  have hev : ∀ᶠ i in l, r i < δ := Filter.Tendsto.eventually_lt_const hδ0 hr
  filter_upwards [hev] with i hi
  refine eLpNorm_mollify_sub_le u hu (ρ i) (hρ0 i) (hρm i) (hρ1 i) ?_
  intro y hy
  have hylt : ‖y‖ < r i := hsupp i y hy
  refine hδ ?_
  rw [dist_eq_norm, sub_zero]
  exact hylt.trans hi
