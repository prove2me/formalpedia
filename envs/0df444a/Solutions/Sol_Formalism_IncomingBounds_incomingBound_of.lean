-- Prove2me | solution 1 for Formalism.IncomingBounds.incomingBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:25.133159+00:00
-- url     : https://prove2.me/submissions/949b1f13-58c8-4292-b7c2-3aefab5e77fb

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_in_reindex
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_fd_part1
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
open FlowDualityReindexing
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) : IncomingBound := by
  intro l d _ hl hd hev D sig hD hopt
  obtain ⟨x, hx, hval⟩ := hF l d hl hd hev D hD
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  have hout : ∀ t : ZMod d, (l : ℝ) * ∑ i ∈ oddLevels d, x t i ≤ D t := by
    intro t
    rw [Finset.mul_sum]
    have h1 : ∑ i ∈ oddLevels d, (l : ℝ) * x t i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x t i :=
      Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (_root_.Formalism.IncomingBounds.FlowDualityReindexing.self_le_pow_of_mem_oddLevels (by linarith) hi) (hx.1 t i)
    have h2 : 0 ≤ ∑ i ∈ oddLevels d, x (t - (i : ZMod d)) i :=
      Finset.sum_nonneg fun i _ => hx.1 _ _
    linarith [hx.2 t]
  calc (∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s), D s)
        = ∑ s ∈ Finset.univ.filter (fun s : ZMod d => 2 / (l : ℝ) ≤ sig s),
            ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_congr rfl fun s hs =>
            (Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s (Finset.mem_filter.1 hs).2 x hx hval).2
      _ ≤ ∑ s : ZMod d, ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun s _ _ => Finset.sum_nonneg fun i _ => hx.1 _ _
      _ = ∑ s : ZMod d, ∑ i ∈ oddLevels d, x s i := Formalism.IncomingBounds.FlowDualityReindexing.in_reindex x
      _ ≤ ∑ s : ZMod d, D s / l :=
          Finset.sum_le_sum fun t _ => by
            rw [le_div_iff₀ hlpos, mul_comm]
            exact hout t
      _ = (∑ s : ZMod d, D s) / l := by rw [Finset.sum_div]
end Formalism.IncomingBounds
