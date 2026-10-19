-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.coe_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T12:32:08.486904+00:00
-- url     : https://prove2.me/submissions/e9c81613-ca31-44c0-8c6c-f9358d783a73

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.coe_sum_single
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) (k : ι) :
    ((∑ i ∈ S, lp.single 2 i (u i) : L2I ι) : ι → ℂ) k = if k ∈ S then u k else 0 := by

  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply, ih]
      by_cases hka : k = a
      · subst hka
        simp [ha]
      · simp [hka, Finset.mem_insert]
