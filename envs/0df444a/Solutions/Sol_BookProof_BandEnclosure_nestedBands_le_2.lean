-- Prove2me | solution 2 for BookProof.BandEnclosure.nestedBands_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:31:21.77771+00:00
-- url     : https://prove2.me/submissions/ca989833-1a11-4f33-890c-6b0728d2e16a

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.nestedBands_le
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterH8
import Definitions.Def_ChapterH6
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.BandEnclosure











noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

set_option maxHeartbeats 1000000 in
theorem solution {lo hi : ℕ → ℝ} (h : NestedBands lo hi) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (lo n) (hi n) ⊆ Set.Icc (lo m) (hi m) := by

  induction n, hmn using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (h n).trans ih
