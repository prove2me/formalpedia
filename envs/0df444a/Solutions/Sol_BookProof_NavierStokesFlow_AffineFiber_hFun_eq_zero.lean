-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T22:07:59.55522+00:00
-- url     : https://prove2.me/submissions/75ba530b-5261-4c81-8bb1-bdb8122562bb

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.hFun_eq_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}
open ShiftHamiltonian

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (S : ShiftData ι) {X : ι → ℂ} {β : ι}
    (hpre : ∀ α, S.shift α = β → X α = 0) (hX : X (S.shift β) = 0) : S.hFun X β = 0 := by

  unfold ShiftData.hFun
  have hhop : S.hop (fun α => (S.amp α : ℂ) * X α) β = 0 := by
    by_cases hb : ∃ α, S.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      rw [ShiftData.hop_shift, hpre α rfl, mul_zero]
    · exact ShiftData.hop_eq_zero S _ hb
  rw [hhop, hX, mul_zero, sub_zero, mul_zero]
