-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.hFun_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T09:49:26.681268+00:00
-- url     : https://prove2.me/submissions/0473ce2f-6e49-45dc-938c-cfb5737c5713

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.hFun_add
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}
open ShiftHamiltonian

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (S : ShiftData ι) (X Y : ι → ℂ) (β : ι) :
    S.hFun (fun α => X α + Y α) β = S.hFun X β + S.hFun Y β := by

  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    simp only [ShiftData.hFun, ShiftData.hop_shift]
    ring
  · have hz : ∀ g : ι → ℂ, S.hop g β = 0 := fun g => ShiftData.hop_eq_zero S g hb
    simp only [ShiftData.hFun, hz]
    ring
