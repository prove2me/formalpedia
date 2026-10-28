-- Prove2me | solution 1 for CycleLengthsExp.BetaGraph.condition_1_claim_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:36:44.913239+00:00
-- url     : https://prove2.me/submissions/435972f3-61a2-43fa-b844-3ca8a84ae720

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

open CycleLengthsExp.BetaGraph in
theorem solution (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 20) (n : ℕ)
    (G : SimpleGraph (Fin n)) (hG : IsBetaGraph β G)
    (S : Set (Fin n)) (hSsize : (1 - β) * n ≤ S.ncard)
    (hS : ∀ U ⊆ S, (U.ncard : ℝ) ≤ β * n →
      (1 - 3 * β) / (2 * β) * U.ncard ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard)
    (U : Set (Fin n)) (hUS : U ⊆ S) (hU0 : 0 < U.ncard) (hU : (U.ncard : ℝ) ≤ β * n) :
    (⌊1 / (4 * β)⌋₊ + 1) * U.ncard + 1 ≤ (CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard := by
  have h1 := hS U hUS hU
  obtain ⟨q, hq⟩ : ∃ q, q = 1 / (4 * β) := ⟨_, rfl⟩
  have hq5 : 5 < q := by
    rw [hq, lt_div_iff₀ (by positivity)]; linarith
  have hrat : (1 - 3 * β) / (2 * β) = 2 * q - 3 / 2 := by
    rw [hq]; field_simp; ring
  have hF : (⌊1 / (4 * β)⌋₊ : ℝ) ≤ q := hq ▸ Nat.floor_le (by positivity)
  have hu : (1 : ℝ) ≤ U.ncard := by exact_mod_cast hU0
  rw [hrat] at h1
  have key : ((⌊1 / (4 * β)⌋₊ : ℝ) + 1) * U.ncard + 1 ≤
      ((CycleLengthsExp.WellSpread.extNbhd G U ∩ S).ncard : ℝ) := by
    nlinarith
  exact_mod_cast key
