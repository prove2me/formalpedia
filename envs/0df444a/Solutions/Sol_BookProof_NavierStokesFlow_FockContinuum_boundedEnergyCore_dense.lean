-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockContinuum.boundedEnergyCore_dense
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:11.065478+00:00
-- url     : https://prove2.me/submissions/34b246a2-9e0e-43bc-b16d-3bffb5c47291
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesFockContinuum.lean — solution of BookProof.NavierStokesFlow.FockContinuum.boundedEnergyCore_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_tendsto_eLpNorm_indicator_compl
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum



open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]

variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in

theorem solution (μ : Measure X) {g : X → ℝ} (hg : Measurable g) :
    Dense ((boundedEnergyCore μ g : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) := by
  have hmeasS : ∀ n : ℕ, MeasurableSet {x | |g x| ≤ (n : ℝ)} :=
    fun n => measurableSet_le hg.abs measurable_const
  intro f
  refine mem_closure_iff_seq_limit.2
    ⟨fun n => ((Lp.memLp f).indicator (hmeasS n)).toLp _, fun n => ?_, ?_⟩
  · refine ⟨n, ?_⟩
    filter_upwards [((Lp.memLp f).indicator (hmeasS n)).coeFn_toLp] with x hx hbig
    rw [hx, Set.indicator_of_notMem (by simpa using hbig)]
  · have heq : ∀ n : ℕ,
        eLpNorm ({x | |g x| ≤ (n : ℝ)}.indicator (f : X → ℂ) - (f : X → ℂ)) 2 μ
          = eLpNorm ({x | |g x| ≤ (n : ℝ)}ᶜ.indicator ((f : X → ℂ))) 2 μ := by
      intro n
      have hfun : {x | |g x| ≤ (n : ℝ)}.indicator (f : X → ℂ) - (f : X → ℂ)
          = -({x | |g x| ≤ (n : ℝ)}ᶜ.indicator (f : X → ℂ)) := by
        funext x
        by_cases h : x ∈ {x | |g x| ≤ (n : ℝ)}
        · simp [Set.indicator_of_mem h,
            Set.indicator_of_notMem (show x ∉ {x | |g x| ≤ (n : ℝ)}ᶜ by simpa using h)]
        · simp [Set.indicator_of_notMem h,
            Set.indicator_of_mem (show x ∈ {x | |g x| ≤ (n : ℝ)}ᶜ from h)]
      rw [hfun, eLpNorm_neg]
    have hten : Filter.Tendsto
        (fun n : ℕ => eLpNorm ({x | |g x| ≤ (n : ℝ)}.indicator (f : X → ℂ) - (f : X → ℂ)) 2 μ)
        Filter.atTop (nhds 0) := by
      simp_rw [heq]
      exact tendsto_eLpNorm_indicator_compl μ hg f
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n : ℕ => {x | |g x| ≤ (n : ℝ)}.indicator (f : X → ℂ))
      (fun n => (Lp.memLp f).indicator (hmeasS n)) (f : X → ℂ) (Lp.memLp f)).2 hten
    rwa [Lp.toLp_coeFn] at h
