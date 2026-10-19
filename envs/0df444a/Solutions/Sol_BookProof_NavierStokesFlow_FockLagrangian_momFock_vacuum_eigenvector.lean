-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.momFock_vacuum_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:46:49.944114+00:00
-- url     : https://prove2.me/submissions/9a58b1dd-54a3-43a8-8d3f-088fcae8c650

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.momFock_vacuum_eigenvector
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_vacState_coeFn
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_vacState_mem_core
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian



open MeasureTheory



open FullEsa FockContinuum
open BookProof.NavierStokesFlow.ThreeComponent

variable {Ω : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution :
    ((momFock.data.hFull ⟨vacState, vacState_mem_core⟩ : momFock.core) : Lp ℂ 2 fockR) = 0 := by

  have key : ((mulD fockR momFock.total_meas momFock.total_dom
      ⟨vacState, vacState_mem_core⟩ : boundedEnergyCore fockR momFock.scale) :
      Lp ℂ 2 fockR) = 0 := by
    refine Lp.ext ?_
    filter_upwards [mulD_coeFn fockR momFock.total_meas momFock.total_dom
        (⟨vacState, vacState_mem_core⟩ : boundedEnergyCore fockR momFock.scale),
      vacState_coeFn, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := fockR)] with x hmul hx hz
    rw [hmul, hz]
    by_cases hmem : x ∈ vacSet
    · obtain ⟨ξ, -, rfl⟩ := hmem
      have h0 : momFock.total (parcelMk 0 ξ) = 0 := by
        rw [momFock_total]
        show 3 / 2 * (∑ k : Fin 0, ξ k) ^ 2 = 0
        simp
      rw [h0]
      simp
    · rw [hx, Set.indicator_of_notMem hmem]
      simp
  rw [momFock.hFull_eq_mulD]
  exact key
