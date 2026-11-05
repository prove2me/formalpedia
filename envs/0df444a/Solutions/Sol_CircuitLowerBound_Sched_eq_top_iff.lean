-- Prove2me | solution 1 for CircuitLowerBound.Sched.eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T02:25:07.384554+00:00
-- url     : https://prove2.me/submissions/55d9ae7a-b702-4da7-adcc-f0a20398b23d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_Sched
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Sched
open ENP Groundwork
variable {α : Type} [Enc α]

private lemma sched_log2_pow_sub_one (n : ℕ) : Nat.log2 (2 ^ n - 1) = n - 1 := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.log2_eq_log_two]
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · rw [Nat.pow_succ]
        have hpos : 0 < 2 ^ n := Nat.pow_pos (by omega)
        omega
      · have hpos : 0 < 2 ^ (n + 1) := Nat.pow_pos (by omega)
        omega

private lemma sched_leTop_mono {a m n : ℕ} (h : m ≤ n) (hm : leTop a m = true) :
    leTop a n = true := by
  simp only [leTop, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
  obtain ⟨hm0, hmlog0, hma⟩ := hm
  have hlog : Nat.log 2 m ≤ Nat.log 2 n := Nat.log_mono_right h
  have hloglog : Nat.log 2 (Nat.log 2 m) ≤ Nat.log 2 (Nat.log 2 n) :=
    Nat.log_mono_right hlog
  simp only [Nat.log2_eq_log_two] at hmlog0 hma ⊢
  refine ⟨by omega, ?_, hma.trans hloglog⟩
  exact ne_of_gt (lt_of_lt_of_le (Nat.pos_of_ne_zero hmlog0) hlog)

private lemma sched_leTop_top (a : ℕ) : leTop a (top a) = true := by
  simp [leTop, top, Nat.log2_eq_log_two]

private lemma sched_leTop_top_pred (a : ℕ) : leTop a (top a - 1) = false := by
  simp [leTop, top, sched_log2_pow_sub_one]

theorem solution (a s : ℕ) : s = top a ↔ (leTop a s && !leTop a (s - 1)) = true := by
  constructor
  · rintro rfl
    simp [sched_leTop_top, sched_leTop_top_pred]
  · intro h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hs, hsp⟩ := h
    rcases lt_trichotomy s (top a) with hst | hst | hst
    · have hle : s ≤ top a - 1 := by omega
      have hbad := sched_leTop_mono hle hs
      rw [sched_leTop_top_pred] at hbad
      contradiction
    · exact hst
    · have hle : top a ≤ s - 1 := by omega
      have hbad := sched_leTop_mono hle (sched_leTop_top a)
      rw [hbad] at hsp
      contradiction
