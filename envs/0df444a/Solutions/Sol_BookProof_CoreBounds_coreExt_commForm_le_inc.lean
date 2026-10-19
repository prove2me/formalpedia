-- Prove2me | solution 1 for BookProof.CoreBounds.coreExt_commForm_le_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:43:00.28013+00:00
-- url     : https://prove2.me/submissions/fd272361-c492-4b51-86a5-1840288f6667

-- Generated from ChapterCoreBoundsEsa.lean — solution of BookProof.CoreBounds.coreExt_commForm_le_inc
import Mathlib
import Definitions.Def_ChapterCoreBoundsEsa
import Theorems.Thm_BookProof_OperatorSeries_commForm_eq_neg_two_im
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
    {A B : ℝ} (hA : CoreRelBound c H₀ A)
    (hcomm : ∀ u : lpFiniteModes ι,
      |(-2 : ℝ) * (inner ℂ (H₀ u) ((diagMax c (inclC c u) : L2I ι)) : ℂ).im|
        ≤ B * (inner ℂ ((u : L2I ι)) ((diagMax c (inclC c u) : L2I ι)) : ℂ).re)
    (x : maxDom c) :
    |commForm (coreExt hA) (diagMax c) x| ≤ B * quadForm (diagMax c) x := by

  have hL : Tendsto (fun S : Finset ι =>
      |(-2 : ℝ) * (inner ℂ (H₀ (trunc c x S))
        ((diagMax c (inclC c (trunc c x S)) : L2I ι)) : ℂ).im|) atTop
      (𝓝 |(-2 : ℝ) * (inner ℂ (coreExt hA x) ((diagMax c x : L2I ι)) : ℂ).im|) := by
    have h := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_coreExt hA x) (tendsto_diag_trunc c x)
    exact ((Complex.continuous_im.tendsto _).comp h).const_mul (-2 : ℝ) |>.abs
  have hR : Tendsto (fun S : Finset ι =>
      B * (inner ℂ ((trunc c x S : lpFiniteModes ι) : L2I ι)
        ((diagMax c (inclC c (trunc c x S)) : L2I ι)) : ℂ).re) atTop
      (𝓝 (B * (inner ℂ ((x : L2I ι)) ((diagMax c x : L2I ι)) : ℂ).re)) := by
    have h := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_trunc c x) (tendsto_diag_trunc c x)
    exact ((Complex.continuous_re.tendsto _).comp h).const_mul B
  have hlim := le_of_tendsto_of_tendsto' hL hR fun S => hcomm (trunc c x S)
  rw [commForm_eq_neg_two_im, quadForm]
  exact hlim
