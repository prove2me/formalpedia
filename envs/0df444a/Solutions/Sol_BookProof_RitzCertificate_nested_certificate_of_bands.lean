-- Prove2me | solution 1 for BookProof.RitzCertificate.nested_certificate_of_bands
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T12:32:06.786425+00:00
-- url     : https://prove2.me/submissions/24be9687-7195-4d77-8d93-2e92eab9b354

import Mathlib
import Definitions.Def_ChapterRitzCertificate
open BookProof.RitzCertificate
open Filter Topology
open BookProof.BandEnclosure

theorem solution {lo hi : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    NestedBands (runLo lo) (runHi hi) ∧ (∀ m, lam ∈ Set.Icc (runLo lo m) (runHi hi m)) ∧
      Tendsto (fun m => runHi hi m - runLo lo m) atTop (𝓝 0) := by
  have mem_range_self (m : ℕ) : m ∈ Finset.range (m + 1) := by simp
  have runLo_mono (lo : ℕ → ℝ) (m : ℕ) : runLo lo m ≤ runLo lo (m + 1) := by
    refine Finset.sup'_le _ _ ?_
    intro k hk
    have hk' : k ∈ Finset.range (m + 1 + 1) := by
      simp only [Finset.mem_range] at hk ⊢
      omega
    exact Finset.le_sup' lo hk'
  have runHi_antitone (hi : ℕ → ℝ) (m : ℕ) : runHi hi (m + 1) ≤ runHi hi m := by
    refine Finset.le_inf' _ _ ?_
    intro k hk
    have hk' : k ∈ Finset.range (m + 1 + 1) := by
      simp only [Finset.mem_range] at hk ⊢
      omega
    exact Finset.inf'_le hi hk'
  have nested : NestedBands (runLo lo) (runHi hi) := by
    intro m
    exact Set.Icc_subset_Icc (runLo_mono lo m) (runHi_antitone hi m)
  have mem (m : ℕ) : lam ∈ Set.Icc (runLo lo m) (runHi hi m) := by
    constructor
    · refine Finset.sup'_le _ _ ?_
      intro k _hk
      exact (hmem k).1
    · refine Finset.le_inf' _ _ ?_
      intro k _hk
      exact (hmem k).2
  have widths :
      Tendsto (fun m => runHi hi m - runLo lo m) atTop (𝓝 0) := by
    have hge : ∀ m, 0 ≤ runHi hi m - runLo lo m := by
      intro m
      have hm := mem m
      linarith [hm.1, hm.2]
    have hle : ∀ m, runHi hi m - runLo lo m ≤ hi m - lo m := by
      intro m
      have hlo : lo m ≤ runLo lo m := Finset.le_sup' lo (mem_range_self m)
      have hhi : runHi hi m ≤ hi m := Finset.inf'_le hi (mem_range_self m)
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hwidth hge hle
  exact ⟨nested, mem, widths⟩
