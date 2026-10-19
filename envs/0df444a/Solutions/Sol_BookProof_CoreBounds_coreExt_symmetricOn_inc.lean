-- Prove2me | solution 1 for BookProof.CoreBounds.coreExt_symmetricOn_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:42:39.069992+00:00
-- url     : https://prove2.me/submissions/dda9c473-023b-4f15-8769-5a8b799aa296

-- Generated from ChapterCoreBoundsEsa.lean — solution of BookProof.CoreBounds.coreExt_symmetricOn_inc
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavineCore
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
theorem solution [DecidableEq ι] {c : ι → ℝ} {H₀ : lpFiniteModes ι →ₗ[ℂ] L2I ι}
    {A : ℝ} (hA : CoreRelBound c H₀ A)
    (hsym : ∀ u v : lpFiniteModes ι,
      (inner ℂ (H₀ u) ((v : L2I ι)) : ℂ) = inner ℂ ((u : L2I ι)) (H₀ v)) :
    SymmetricOn (maxDom c) (coreExt hA) := by

  intro x y
  have hL : Tendsto (fun S : Finset ι =>
      (inner ℂ (H₀ (trunc c x S)) ((trunc c y S : lpFiniteModes ι) : L2I ι) : ℂ)) atTop
      (𝓝 (inner ℂ (coreExt hA x) ((y : L2I ι)) : ℂ)) :=
    ((tendsto_coreExt hA x).inner (tendsto_trunc c y))
  have hR : Tendsto (fun S : Finset ι =>
      (inner ℂ ((trunc c x S : lpFiniteModes ι) : L2I ι) (H₀ (trunc c y S)) : ℂ)) atTop
      (𝓝 (inner ℂ ((x : L2I ι)) (coreExt hA y) : ℂ)) :=
    ((tendsto_trunc c x).inner (tendsto_coreExt hA y))
  refine tendsto_nhds_unique hL (hR.congr fun S => ?_)
  exact (hsym (trunc c x S) (trunc c y S)).symm
