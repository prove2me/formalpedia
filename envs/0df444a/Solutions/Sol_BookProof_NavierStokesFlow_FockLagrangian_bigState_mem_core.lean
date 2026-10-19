-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:03:44.74395+00:00
-- url     : https://prove2.me/submissions/96899e3b-c1ab-4dd1-8d14-2fcc94506216

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.bigState_mem_core
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution {K : ℝ} (hK : 0 ≤ K) : bigState K ∈ momFock.core := by

  refine ⟨⌈3 * (K + 1)⌉₊, ?_⟩
  filter_upwards [bigState_coeFn K] with x hx hbig
  rw [hx]
  by_cases hmem : x ∈ bigSet K
  · exfalso
    apply hbig
    obtain ⟨ξ, hξ, rfl⟩ := hmem
    have h0 : ξ 0 ∈ Set.Icc K (K + 1) := hξ 0 (Set.mem_univ 0)
    have hnn : 0 ≤ ξ 0 := le_trans hK h0.1
    have hs : |momFock.scale (parcelMk 1 ξ)| = 3 * ξ 0 := by
      rw [momFock_scale]
      show abs (3 * abs (∑ k : Fin 1, ξ k)) = 3 * ξ 0
      rw [Fin.sum_univ_one, abs_of_nonneg hnn, abs_of_nonneg (by positivity)]
    rw [hs]
    calc 3 * ξ 0 ≤ 3 * (K + 1) := by linarith [h0.2]
      _ ≤ (⌈3 * (K + 1)⌉₊ : ℝ) := Nat.le_ceil _
  · exact Set.indicator_of_notMem hmem _
