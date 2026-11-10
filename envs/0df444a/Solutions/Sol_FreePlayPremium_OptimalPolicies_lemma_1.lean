-- Prove2me | solution 1 for FreePlayPremium.OptimalPolicies.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T10:37:56.270093+00:00
-- url     : https://prove2.me/submissions/ac7e698e-0532-4cc0-b09b-59e2420ab0e6

import Definitions.Def_FreePlayPremium_OptimalPolicies_Players

open Set FreePlayPremium.OptimalPolicies

theorem solution :
    ¬ (∀ (P : PlayerParameters) (hP : P.Valid) (hdu : P.up < P.down),
      (∀ p : ℝ, 0 ≤ p →
        (premiumShare P p ∈ Icc 0 1 ∧
         ∀ s ∈ Icc (0 : ℝ) 1, Stable P p s ↔ s = premiumShare P p)) ∧
      (∀ p ∈ Icc P.up P.down, interiorShare P p ∈ Icc (0 : ℝ) 1) ∧
      StrictAntiOn (interiorShare P) (Icc P.up P.down)) := by
  intro h
  let P : PlayerParameters := ⟨3, 2, 1⟩
  have hP : P.Valid := by
    dsimp [PlayerParameters.Valid, P]
    norm_num
  have hdu : P.up < P.down := by
    dsimp [P]
    norm_num
  have h1 := ((h P hP hdu).1 2 (by norm_num)).2 0 (by simp)
  have hps : (0 : ℝ) = premiumShare P 2 := by
    dsimp [premiumShare, interiorShare, P]
    norm_num
  have hstab : Stable P 2 0 := h1.mpr hps
  dsimp [Stable, utilityDifference, P] at hstab
  rcases hstab with ⟨_, hlt⟩ | ⟨heq, _⟩ | ⟨hlt, _⟩ <;> linarith
