-- Prove2me | solution 1 for ClauseBound.Gen.Rate.rest_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:09.258669+00:00
-- url     : https://prove2.me/submissions/3d15257c-00ae-469f-9c7d-e4320e4866fe

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Gen_RateAux
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Gen ClauseBound.Gen.Rate
open Nat (size)
namespace ClauseBound.Gen.Rate
theorem _root_.solution (g c lam B bits sd R sp : ℕ) (hc : 1 ≤ c) (hlam : 1 ≤ lam) (hg : 6 ≤ g) (hbits : bits ≤ (2 * lam) ^ c)
    (hsd : sd ≤ (2 * lam) ^ c) (hR : R ≤ g ^ 4) (hsp : sp ≤ R * (2 * lam) ^ c + 1) :
    R * sd + (g * g) ^ 2 * lam + g ^ 2 * (g * B + g ^ 2 * bits + 1) + 2 + 2 * sp ≤ (g ^ 2 * (lam + B)) ^ (c + 3) := by
  obtain ⟨a, ha⟩ : ∃ a, a = g ^ 2 := ⟨_, rfl⟩
  have hga : g ≤ a := by rw [ha, sq]; exact Nat.le_mul_of_pos_left _ (by omega)
  have ha6 : 6 ≤ a := by omega
  have hg4 : g ^ 4 = a * a := by rw [ha]; ring
  have hgg : (g * g) ^ 2 = a * a := by rw [ha]; ring
  rw [hg4] at hR
  rw [hgg, ← ha]
  obtain ⟨X, hX⟩ : ∃ X, X = a * (lam + B) := ⟨_, rfl⟩
  rw [← hX]
  have haX : a ≤ X := by rw [hX]; exact Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ c := ⟨_, rfl⟩
  have hXY : X ≤ Y := by rw [hY]; exact Nat.le_self_pow (by omega) X
  have hY1 : 1 ≤ Y := by omega
  have h1 : a * lam ≤ Y := le_trans (by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)) hXY
  have h2 : a * B ≤ Y := le_trans (by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)) hXY
  have h2l : 2 * lam ≤ X := by
    calc 2 * lam ≤ a * lam := Nat.mul_le_mul_right _ (by omega)
      _ ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have ht : (2 * lam) ^ c ≤ Y := by rw [hY]; exact Nat.pow_le_pow_left h2l c
  have h3 : bits ≤ Y := hbits.trans ht
  have h4 : sd ≤ Y := hsd.trans ht
  have hgB : g * B ≤ Y := le_trans (Nat.mul_le_mul_right _ hga) h2
  have h5 : sp ≤ a * a * Y + Y := by
    calc sp ≤ R * (2 * lam) ^ c + 1 := hsp
      _ ≤ a * a * Y + Y := by gcongr
  have h6 : a * a * lam ≤ a * Y := by
    calc a * a * lam = a * (a * lam) := by ring
      _ ≤ a * Y := by gcongr
  have q1 : 6 * a ≤ a ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ ha6
  have q2 : 6 * a ^ 2 ≤ a ^ 3 := by rw [pow_succ a 2, mul_comm]; exact Nat.mul_le_mul_left _ ha6
  calc R * sd + a * a * lam + a * (g * B + a * bits + 1) + 2 + 2 * sp
      ≤ a * a * Y + a * Y + a * (Y + a * Y + Y) + 2 * Y + 2 * (a * a * Y + Y) := by gcongr; omega
    _ = (4 * a ^ 2 + 3 * a + 4) * Y := by ring
    _ ≤ a ^ 3 * Y := Nat.mul_le_mul_right _ (by omega)
    _ ≤ X ^ 3 * Y := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left haX 3)
    _ = X ^ (c + 3) := by rw [hY]; ring
end ClauseBound.Gen.Rate
