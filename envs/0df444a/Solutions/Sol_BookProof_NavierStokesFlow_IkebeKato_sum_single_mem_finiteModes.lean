-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:55.357306+00:00
-- url     : https://prove2.me/submissions/2c0489f9-ff29-45be-b9c2-e8b2b1cb04b2

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.sum_single_mem_finiteModes
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) :
    (∑ i ∈ S, lp.single 2 i (u i) : L2I ι) ∈ lpFiniteModes ι := Submodule.sum_mem _ fun i _ => lpSingle_mem_lpFiniteModes i (u i)
