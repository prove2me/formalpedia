-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyOfEventuallyShellwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:19:17.776924+00:00
-- url     : https://prove2.me/submissions/fc78ffee-6f46-4bcb-b2ea-955aec8f1263

import Definitions.Def_FirstPassageLinearTransport_ClockBudget
import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : ℕ → ℕ → Prop)
    (hP : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M → P M n) :
    ∀ᶠ n : ℕ in atTop, 0 < n → P (Nat.log 2 n) n := by
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hP
  filter_upwards [eventually_ge_atTop (2 ^ M0)] with n hn
  intro hnpos
  have hlog : M0 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hn
  exact hM0 (Nat.log 2 n) hlog n hnpos (mem_dyadicShell_log hnpos)
end FirstPassageLinearTransport
