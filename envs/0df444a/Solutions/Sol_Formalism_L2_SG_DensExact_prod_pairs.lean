-- Prove2me | solution 1 for Formalism.L2.SG.DensExact.prod_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:17:44.740606+00:00
-- url     : https://prove2.me/submissions/2f958090-2e81-4eda-90fe-dd0309e5c2fc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.DensExact
namespace Formalism.L2.SG.DensExact
theorem _root_.solution (f : ℕ → ℝ) : ∀ (c N : ℕ), 2 * c ≤ N →
    ∏ i ∈ range c, (f (N - 2 * i) * f (N - 2 * i - 1)) = ∏ j ∈ Ico (N + 1 - 2 * c) (N + 1), f j := by
  intro c
  induction c with
  | zero => intro N _; simp
  | succ c ih =>
    intro N hN
    rw [prod_range_succ, ih N (by omega)]
    have h1 : N + 1 - 2 * (c + 1) < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h1]
    have h2 : N + 1 - 2 * (c + 1) + 1 < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h2]
    have e1 : N + 1 - 2 * (c + 1) + 1 + 1 = N + 1 - 2 * c := by omega
    have e3 : N + 1 - 2 * (c + 1) + 1 = N - 2 * c := by omega
    have e2 : N + 1 - 2 * (c + 1) = N - 2 * c - 1 := by omega
    rw [e1, e3, e2]
    ring
end Formalism.L2.SG.DensExact
