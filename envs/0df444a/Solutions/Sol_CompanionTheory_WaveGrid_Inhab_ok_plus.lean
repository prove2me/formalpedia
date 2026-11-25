-- Prove2me | solution 1 for CompanionTheory.WaveGrid.Inhab.ok_plus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:36.89081+00:00
-- url     : https://prove2.me/submissions/50b5e447-52c4-4313-a9c3-2bbf729cb139

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_PStarTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_CfgTie
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_NqOfLamData
import Theorems.Thm_CompanionTheory_WaveGrid_Inhab_int_of_half
import Theorems.Thm_CompanionTheory_WaveGrid_inter_half


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Inhab
open Formalism.FourierDecayAlt Finset CompanionTheory.WaveGrid GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
namespace CompanionTheory.WaveGrid.Inhab
theorem _root_.solution (k r : ℕ) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ)
    (b : ℝ) (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hu : HypType k r lam u b) (l n₀ : ℕ) (hl1 : 1 ≤ l) (hlk : l < k)
    (hposition : (2 * n₀ + 1 : ℝ) ≤ u l - u (l + 1)) : (⟨k, r, T, T', u, uP u l n₀⟩ : M.Par).OK := by
  have hk : 1 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
  refine ⟨hk, hT, hT', int_of_half hk hu.half hu.half, ?_, ?_⟩
  · intro i hi
    obtain ⟨n, hn⟩ := int_of_half hk hu.half hu.half i hi
    by_cases h : i = l + 1
    · refine ⟨n + n₀, ?_⟩
      simp only [uP, if_pos h]
      push_cast
      linarith
    · refine ⟨n, ?_⟩
      simp only [uP, if_neg h]
      exact hn
  · intro i hi
    obtain ⟨hi1, hik⟩ := Finset.mem_Icc.1 hi
    obtain ⟨a1, a2⟩ := inter_half hc hu i hi1 hik
    simp only [M.Par.lo, M.Par.hi, uP]
    by_cases h1 : i + 1 = l + 1
    · have hil : i = l := by omega
      subst hil
      have h2 : ¬ (i = i + 1) := by omega
      rw [if_pos h1, if_neg h2, min_self, max_eq_right (by linarith)]
      linarith
    · by_cases h2 : i = l + 1
      · rw [if_neg h1, if_pos h2, max_self, min_eq_left (by linarith)]
        linarith
      · rw [if_neg h1, if_neg h2, max_self, min_self]
        linarith
end CompanionTheory.WaveGrid.Inhab
