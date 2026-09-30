-- Prove2me | solution 2 for BookProof.BandEnclosure.band_limit_unique
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T22:20:38.645905+00:00
-- url     : https://prove2.me/submissions/92a41668-b4b0-4f64-b2de-da15522345af

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.band_limit_unique
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
theorem solution {lo hi : ℕ → ℝ} {lam lam' : ℝ}
    (h : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) (h' : ∀ m, lam' ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    lam = lam' := by

  have habs : ∀ m, |lam - lam'| ≤ hi m - lo m := by
    intro m
    rw [abs_sub_le_iff]
    exact ⟨by linarith [(h m).2, (h' m).1], by linarith [(h' m).2, (h m).1]⟩
  have hle : |lam - lam'| ≤ 0 :=
    ge_of_tendsto hwidth (Filter.Eventually.of_forall habs)
  have : lam - lam' = 0 := by
    have := abs_nonneg (lam - lam')
    have h0 : |lam - lam'| = 0 := le_antisymm hle this
    exact abs_eq_zero.mp h0
  linarith
