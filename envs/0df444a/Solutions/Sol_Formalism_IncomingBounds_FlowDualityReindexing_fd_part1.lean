-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.fd_part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:22.427717+00:00
-- url     : https://prove2.me/submissions/22c3abd1-c857-40d6-b423-31c679957d4e

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_optdual_maxFlow
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_cs_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
namespace FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
private theorem one_le_of_mem_oddLevels {i : ℕ} (hi : i ∈ oddLevels d) : 1 ≤ i := by
  obtain ⟨k, rfl⟩ := (Finset.mem_filter.1 hi).2
  omega
private theorem self_le_pow_of_mem_oddLevels (hl : (1 : ℝ) ≤ l) {i : ℕ} (hi : i ∈ oddLevels d) :
    (l : ℝ) ≤ (l : ℝ) ^ i := by
  calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ hl (one_le_of_mem_oddLevels hi)
end FlowDualityReindexing
open FlowDualityReindexing
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowDualityReindexing
theorem _root_.solution (hl : 3 ≤ l) (D sig : ZMod d → ℝ) (hopt : IsOptDual l d D sig) (s : ZMod d)
    (hs : 2 / (l : ℝ) ≤ sig s) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x)
    (hval : flowVal d x = maxFlow l d D) :
    (∀ i ∈ oddLevels d, x s i = 0) ∧ D s = ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i := by
  have hF := optdual_maxFlow D sig hopt
  obtain ⟨h1, h2⟩ := cs_zero D sig x hx hopt.1 (hval.trans hF)
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hsig := hopt.1.1
  have hl2 : (l : ℝ) * (2 / l) = 2 := by field_simp
  have h2l : 2 ≤ (l : ℝ) * sig s := by
    have := mul_le_mul_of_nonneg_left hs hlpos.le
    linarith
  have hout : ∀ i ∈ oddLevels d, x s i = 0 := by
    intro i hi
    have hpow := self_le_pow_of_mem_oddLevels (l := l) (by linarith) hi
    have hred : 0 < (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1 := by
      have := mul_le_mul_of_nonneg_right hpow (hsig s).1
      linarith [(hsig (s + (i : ZMod d))).1]
    rcases mul_eq_zero.1 (h2 s i hi) with h | h
    · exact h
    · linarith
  refine ⟨hout, ?_⟩
  have hs0 : 0 < sig s := by nlinarith
  rcases mul_eq_zero.1 (h1 s) with h | h
  · linarith
  have hz : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hout i hi, mul_zero]
  rw [hz] at h
  linarith
end Formalism.IncomingBounds.FlowDualityReindexing
