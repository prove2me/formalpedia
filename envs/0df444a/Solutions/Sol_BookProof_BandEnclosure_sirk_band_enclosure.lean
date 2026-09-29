-- Prove2me | solution 1 for BookProof.BandEnclosure.sirk_band_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:24.322253+00:00
-- url     : https://prove2.me/submissions/58e0c692-be23-4087-80d5-76960e88f0e9

-- Generated from ChapterBandEnclosure.lean — solution of BookProof.BandEnclosure.sirk_band_enclosure
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Theorems.Thm_BookProof_BandEnclosure_band_enclosure_endpoints_tendsto
import Theorems.Thm_BookProof_BandEnclosure_sirk_nestedBands
import Theorems.Thm_BookProof_BandEnclosure_sirk_band_widths_tendsto_zero
open BookProof.BandEnclosure











noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8

set_option maxHeartbeats 1000000 in
theorem solution (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 < h)
    {a : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, a m ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m))
    (hconv : Tendsto a atTop (𝓝 lam)) :
    (∀ m, lam ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m)) ∧
      (∀ lam', (∀ m, lam' ∈ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m)) → lam' = lam) ∧
      Tendsto (fun m => sirkBound C Dmin h nv m) atTop (𝓝 lam) := by

  obtain ⟨h1, h2, -, h4⟩ :=
    band_enclosure_endpoints_tendsto (sirk_nestedBands C Dmin h nv hC hD hnv hh.le) hmem hconv
      (sirk_band_widths_tendsto_zero C Dmin h nv hh)
  exact ⟨h1, h2, h4⟩
