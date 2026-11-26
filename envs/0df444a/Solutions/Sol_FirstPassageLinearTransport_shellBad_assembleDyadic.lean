-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_assembleDyadic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:09.730255+00:00
-- url     : https://prove2.me/submissions/86fc5962-c757-41ae-a343-bdf73651eda8

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : ℕ → Set ℕ) (M : ℕ) :
    shellBad (assembleDyadic S) M = shellBad (S M) M := by
  classical
  ext n
  simp only [shellBad, Finset.mem_filter, assembleDyadic, Set.mem_setOf_eq]
  by_cases hn : n ∈ dyadicShell M
  · have hlog : Nat.log 2 n = M := by
      rw [mem_dyadicShell] at hn
      exact Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
    rw [hlog]
  · simp [hn]
end FirstPassageLinearTransport
