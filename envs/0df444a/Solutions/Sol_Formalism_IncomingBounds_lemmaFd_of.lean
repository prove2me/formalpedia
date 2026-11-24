-- Prove2me | solution 1 for Formalism.IncomingBounds.lemmaFd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:53:26.506679+00:00
-- url     : https://prove2.me/submissions/abd654c8-1e85-4579-8169-2783f7f8586e

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_flow_le
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_sum_inv_pow_le
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_fd_part1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
open FlowDualityReindexing
namespace Formalism.IncomingBounds
theorem _root_.solution (hF : FlowAttained) (hA : LemmaFa) : LemmaFd := by
  intro l d _ hl hd hev D sig hD hopt s hs
  have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
  have hlpos : (0 : ℝ) < l := by linarith
  refine ⟨fun x hx hval => Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s hs x hx hval, ?_⟩
  obtain ⟨x, hx, hval⟩ := hF l d hl hd hev D hD
  have hsat := (Formalism.IncomingBounds.FlowDualityReindexing.fd_part1 hl D sig hopt s hs x hx hval).2
  have hb : D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i := by
    rw [hsat]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [le_div_iff₀ (pow_pos hlpos i), mul_comm]
    exact Formalism.IncomingBounds.FlowDualityReindexing.flow_le D x hx (s - (i : ZMod d)) i hi
  refine ⟨hb, fun _ => ?_⟩
  obtain ⟨s', hs'⟩ := Finite.exists_max D
  refine ⟨s', ?_⟩
  have hP : 0 < gam l := by
    unfold gam
    exact div_pos hlpos (by nlinarith)
  rw [div_le_iff₀ hP]
  calc D s ≤ ∑ i ∈ oddLevels d, D (s - (i : ZMod d)) / (l : ℝ) ^ i := hb
    _ ≤ ∑ i ∈ oddLevels d, D s' * ((l : ℝ) ^ i)⁻¹ :=
        Finset.sum_le_sum fun i _ => by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (hs' _) (by positivity)
    _ = D s' * ∑ i ∈ oddLevels d, ((l : ℝ) ^ i)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ D s' * gam l :=
        mul_le_mul_of_nonneg_left (Formalism.IncomingBounds.FlowDualityReindexing.sum_inv_pow_le hl) (hD s')
end Formalism.IncomingBounds
