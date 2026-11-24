-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.first_kind_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:08.162071+00:00
-- url     : https://prove2.me/submissions/170cc316-4796-41f2-b720-4110186f1ac3

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_band_exponent_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_band_root_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_first_kind_bucket_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : FirstKind := by
  obtain ⟨C, hC⟩ := first_kind_bucket_bound
  refine ⟨C, ?_⟩
  intro e J Y X' ρ p₀ s h1 h2 h3 h4 h5 h6 h7 h8
  refine hC e J ⌊Real.log X'⌋₊ Y X' ρ p₀ (fun i => X' ^ ((1 : ℝ) / ((i + 1 : ℕ) : ℝ))) s h1 h2 h3 h4 h5
    (by linarith) ?_ ?_
  · intro i _
    have hx : (1 : ℝ) ≤ X' := by linarith
    have hpos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have h0 : (0 : ℝ) ≤ (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by positivity
    have h1' : (1 : ℝ) / ((i + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    refine ⟨Real.one_le_rpow hx h0, ?_⟩
    calc X' ^ ((1 : ℝ) / ((i + 1 : ℕ) : ℝ)) ≤ X' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1'
      _ = X' := Real.rpow_one X'
  · intro p hp
    obtain ⟨a1, a2, a3⟩ := h8 p hp
    refine ⟨a1, a2, ?_⟩
    rcases a3 with a3 | ⟨b1, i, b2, b3, b4⟩
    · exact Or.inl a3
    · right
      have hp8 : 8 ≤ p := by
        have : (8 : ℝ) ≤ p := le_trans h6 b1
        exact_mod_cast this
      have hi := band_exponent_bound X' ρ p i h7 (by linarith) hp8 b4
      have hi' : i ≤ ⌊Real.log X'⌋₊ := Nat.le_floor hi
      obtain ⟨c1, c2⟩ := band_root_bound X' ρ p i (by linarith) h4 (by linarith) (Nat.cast_nonneg p) b2 b3 b4
      refine ⟨i - 1, by omega, b1, ?_, ?_⟩
      · have : i - 1 + 1 = i := Nat.sub_add_cancel b2
        simp only [this]; exact c1
      · have : i - 1 + 1 = i := Nat.sub_add_cancel b2
        simp only [this]; exact c2
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
