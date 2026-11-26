-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_badCount_assembleDyadic_le_polylog_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:27.0928+00:00
-- url     : https://prove2.me/submissions/ba215fdb-5637-4087-af77-21c4974d8705

import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Theorems.Thm_FirstPassageLinearTransport_badCount_assembleDyadic_le_polylog_profile
import Theorems.Thm_FirstPassageLinearTransport_tendsto_halfNatLogTwo_atTop
import Theorems.Thm_FirstPassageLinearTransport_eventually_two_pow_halfNatLog_le_polylog
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
open Filter
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (S : ℕ → Set ℕ) (M₀ : ℕ) (B kappa : ℝ)
    (hB : 0 ≤ B) (hkappa : 0 ≤ kappa)
    (hshell : ∀ M, M₀ ≤ M →
      shellExceptionalRatio (S M) M ≤
        B * (((M : ℝ) + 2) ^ (-kappa))) :
    ∀ᶠ N : ℕ in atTop,
      (badCount (assembleDyadic S) N : ℝ) ≤
        (1 + 2 * B) * N *
          ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
  have hEarly := eventually_two_pow_halfNatLog_le_polylog hkappa
  have hHalfT := tendsto_halfNatLogTwo_atTop
  have hM₀ : ∀ᶠ N : ℕ in atTop, M₀ ≤ (Nat.log 2 N) / 2 :=
    hHalfT.eventually (eventually_ge_atTop M₀)
  filter_upwards [hEarly, hM₀, eventually_ge_atTop (1 : ℕ)]
    with N hEarly hM₀ hN1
  have hraw := badCount_assembleDyadic_le_polylog_profile
    S M₀ N B kappa hB hkappa hshell (by omega) hM₀
  let xpow : ℝ :=
    ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa)
  calc
    (badCount (assembleDyadic S) N : ℝ) ≤
        (2 : ℝ) ^ ((Nat.log 2 N) / 2) +
          2 * B * N * xpow := by simpa [xpow] using hraw
    _ ≤ (N : ℝ) * xpow + 2 * B * N * xpow :=
      by
        simpa [add_comm] using
          add_le_add_right (by simpa [xpow] using hEarly)
            (2 * B * (N : ℝ) * xpow)
    _ = (1 + 2 * B) * N * xpow := by ring
    _ = (1 + 2 * B) * N *
        ((((Nat.log 2 N) / 2 : ℕ) : ℝ) + 2) ^ (-kappa) := by
      rfl
end FirstPassageLinearTransport
