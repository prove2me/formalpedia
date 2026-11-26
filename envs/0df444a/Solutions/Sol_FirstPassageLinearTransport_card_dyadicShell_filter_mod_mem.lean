-- Prove2me | solution 1 for FirstPassageLinearTransport.card_dyadicShell_filter_mod_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:21:58.389173+00:00
-- url     : https://prove2.me/submissions/88a43118-6183-4705-8943-4d4412a54e5e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
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


attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
namespace FirstPassageLinearTransport
theorem _root_.solution
    (M : ℕ) (S : Finset (Fin (2 ^ M))) :
    ((dyadicShell M).filter
      (fun n =>
        (⟨n % (2 ^ M), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ M)) ∈ S)).card = S.card := by
  classical
  let q := 2 ^ M
  have hq : 0 < q := pow_pos (by omega) _
  apply Finset.card_bij
      (fun n hn =>
        (⟨n - q, by
          have hnShell := (Finset.mem_filter.mp hn).1
          have hnBounds := mem_dyadicShell.mp hnShell
          have hupper : n < q + q := by
            dsimp [q]
            simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using hnBounds.2
          omega⟩ : Fin q))
  · intro n hn
    have hnS := (Finset.mem_filter.mp hn).2
    have hnShell := (Finset.mem_filter.mp hn).1
    have hnLower := (mem_dyadicShell.mp hnShell).1
    have hnEq : q + (n - q) = n := Nat.add_sub_of_le hnLower
    have hmod : n % q = n - q := by
      calc
        n % q = (q + (n - q)) % q := by rw [hnEq]
        _ = (n - q) % q := by simp [Nat.add_mod]
        _ = n - q := Nat.mod_eq_of_lt (by
          have hnBounds := mem_dyadicShell.mp hnShell
          have hupper : n < q + q := by
            dsimp [q]
            simpa [pow_succ, Nat.mul_comm, Nat.two_mul] using hnBounds.2
          omega)
    simpa [q, hmod] using hnS
  · intro n hn m hm hnm
    have hnLower := (mem_dyadicShell.mp (Finset.mem_filter.mp hn).1).1
    have hmLower := (mem_dyadicShell.mp (Finset.mem_filter.mp hm).1).1
    have hval : n - q = m - q := congrArg Fin.val hnm
    omega
  · intro x hx
    refine ⟨q + (x : ℕ), ?_, ?_⟩
    · simp only [Finset.mem_filter]
      constructor
      · rw [mem_dyadicShell]
        constructor
        · dsimp [q]
          omega
        · have hxlt := x.isLt
          dsimp [q] at hxlt ⊢
          rw [pow_succ]
          omega
      · have hmod : (q + (x : ℕ)) % q = (x : ℕ) := by
          simp [Nat.add_mod, Nat.mod_eq_of_lt x.isLt]
        simpa [q, hmod] using hx
    · apply Fin.ext
      simp
end FirstPassageLinearTransport
