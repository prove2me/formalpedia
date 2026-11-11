-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18m_subsigma_L1_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:24:52.45626+00:00
-- url     : https://prove2.me/submissions/fdd28247-ea43-4c9c-9993-2b5290375a3f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Closedness of the original sub-sigma-algebra L1 subspace
under L1 norm convergence on the same probability measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hSub : m ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n : ℕ, AEStronglyMeasurable[m] (f n) P)
    (hfi : ∀ n : ℕ, MemLp (f n) 1 P)
    (hgi : MemLp g 1 P)
    (hNorm : Tendsto (fun n : ℕ => eLpNorm (f n - g) 1 P)
      atTop (𝓝 (0 : ℝ≥0∞))) :
    AEStronglyMeasurable[m] g P := by
  let F : ℕ → Lp ℝ 1 P := fun n => MemLp.toLp (f n) (hfi n)
  let G : Lp ℝ 1 P := MemLp.toLp g hgi
  have hT : Tendsto F atTop (𝓝 G) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfi g hgi).2 hNorm
  have hClosed :
      IsClosed {u : Lp ℝ 1 P |
        AEStronglyMeasurable[m] (u : Ω → ℝ) P} :=
    isClosed_aestronglyMeasurable hSub
  have hF (n : ℕ) : F n ∈
      {u : Lp ℝ 1 P |
        AEStronglyMeasurable[m] (u : Ω → ℝ) P} := by
    exact (hf n).congr (MemLp.coeFn_toLp (hfi n)).symm
  have hG : G ∈
      {u : Lp ℝ 1 P |
        AEStronglyMeasurable[m] (u : Ω → ℝ) P} :=
    hClosed.mem_of_tendsto hT (Filter.Eventually.of_forall hF)
  exact hG.congr (MemLp.coeFn_toLp hgi)
