-- Prove2me | solution 1 for BookProof.CoreBounds.coreExt_core_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:42:16.801237+00:00
-- url     : https://prove2.me/submissions/9412b8ec-0043-4367-96aa-c46a0f1318fc

-- Generated from ChapterCoreBoundsEsa.lean — solution of BookProof.CoreBounds.coreExt_core_inc
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.CoreBounds




open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries
open Filter Topology
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

variable {ι : Type*} {c : ι → ℝ}

variable {ι : Type*} {c : ι → ℝ}
variable (H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι) (A : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι} {A : ℝ}
    (hA : CoreRelBound c H₀ A) (u : lpFiniteModes ι) :
    coreExtFun c H₀ (inclC c u) = H₀ u := by

  classical
  have hfin : (Function.support ((u : L2I ι) : ι → ℂ)).Finite := u.2
  have heq : ∀ S : Finset ι, hfin.toFinset ⊆ S → trunc c (inclC c u) S = u := by
    intro S hS
    ext k
    rw [trunc_coe]
    by_cases hk : k ∈ S
    · simp [hk]
    · have : ((u : L2I ι) : ι → ℂ) k = 0 := by
        by_contra hne
        exact hk (hS (by simpa [Set.Finite.mem_toFinset, Function.mem_support] using hne))
      simp [hk, this]
  have : Tendsto (fun S : Finset ι => H₀ (trunc c (inclC c u) S)) atTop (𝓝 (H₀ u)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with S hS
    rw [heq S hS]
  exact tendsto_nhds_unique (tendsto_coreExt hA (inclC c u)) this
