-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockLagrangian.fockR_total_level
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T21:08:52.077051+00:00
-- url     : https://prove2.me/submissions/4e8ae710-d2f5-4c75-87c3-ce339d33f2c4

-- Generated from ChapterNavierStokesFockParcels.lean — solution of BookProof.NavierStokesFlow.FockLagrangian.fockR_total_level
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_volume_sum_sq_level
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
theorem solution {r : ℝ} (hr : r ≠ 0) :
    fockR {x | momFock.total x = r} = 0 := by

  have hmeas : MeasurableSet {x : ParcelConf ℝ | momFock.total x = r} :=
    momFock.total_meas (measurableSet_singleton r)
  rw [fockMeasure_apply (volume : Measure ℝ) hmeas]
  have hz : ∀ n : ℕ,
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
        (parcelMk n ⁻¹' {x : ParcelConf ℝ | momFock.total x = r}) = 0 := by
    intro n
    have hpre : (parcelMk n ⁻¹' {x : ParcelConf ℝ | momFock.total x = r})
        = {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = 2 * r / 3} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, momFock_total, parcelMk]
      constructor
      · intro h; linarith
      · intro h; rw [h]; ring
    rw [hpre]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hempty : {ξ : Fin 0 → ℝ | (∑ i, ξ i) ^ 2 = 2 * r / 3} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => ?_
        simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty] at hξ
        exact hr (by linarith)
      rw [hempty, measure_empty]
    · rw [← volume_pi]
      exact volume_sum_sq_level n hn _
  rw [tsum_congr hz, tsum_zero]
