-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.isPosCol_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:10.607574+00:00
-- url     : https://prove2.me/submissions/cedbc2d7-4078-408e-8b3a-8c670c9f1fb1

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.isPosCol_add
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution {a b : ℕ → (ℕ →₀ ℂ)} (ha : IsPosCol a) (hb : IsPosCol b) :
    IsPosCol (fun k => a k + b k) := by

  intro S c
  have hsplit : (∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * ((a k + b k) j) * c k)
      = (∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (a k) j * c k)
        + ∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (b k) j * c k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finsupp.add_apply]
    ring
  rw [hsplit, Complex.add_re]
  exact add_nonneg (ha S c) (hb S c)
