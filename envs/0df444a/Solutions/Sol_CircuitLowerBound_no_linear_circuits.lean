-- Prove2me | solution 1 for CircuitLowerBound.no_linear_circuits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:15:04.696281+00:00
-- url     : https://prove2.me/submissions/8cac36d6-5c6e-4d32-9251-35bb03c56a4e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Main
import Theorems.Thm_CircuitLowerBound_Acc_mono
import Theorems.Thm_CircuitLowerBound_sat_nil
import Theorems.Thm_CircuitLowerBound_not_sat_nil_clause
import Theorems.Thm_CircuitLowerBound_sat_by_circuit
import Theorems.Thm_CircuitLowerBound_room

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
namespace CircuitLowerBound
theorem _root_.solution (hTab : StTab) (hCode : StCode) (hChain : StChain) (hV : StVars) (hG : StGreedy) (hAlg : StAlg) : ¬HasLinearCircuits L0 := by
  rintro ⟨c₀, hc⟩
  obtain ⟨N, hfin, hsound, hcomp⟩ := hAlg c₀
  obtain ⟨e, he⟩ := hTab N hfin
  obtain ⟨m₀, hm₀⟩ := hcomp e
  obtain ⟨a, ha, hae⟩ := hCode e (m₀ + (4 * (kb e + lam e) + 64))
  have h2a : a < 2 ^ a := Nat.lt_two_pow_self
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℕ, ∀ s, p s = 2 ^ a * (2 * s + 1) := ⟨_, fun _ => rfl⟩
  have hnu : ∀ s, nu (p s) = a := fun s => by rw [hp]; exact (hChain a s).1
  have hpos : ∀ s, pos (p s) = s := fun s => by rw [hp]; exact (hChain a s).2
  have hnext : ∀ s, next (p s) = p (s + 1) := fun s => by rw [next, hnu, hp, hp, pow_succ]; ring
  have hbig : ∀ s, 2 ^ a ≤ p s := fun s => by rw [hp]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h3 : ∀ s, p (s + 1) ≤ 3 * p s := fun s => by
    rw [hp, hp]
    have : 0 < 2 ^ a := by positivity
    nlinarith
  -- the machine accepts a number of the chain if and only if its formula is satisfiable
  have hacc : ∀ s, s ≤ top a → Sat (Phi (p s)) → Acc N (p s) (2 ^ (p s / 8)) := by
    intro s hs hsat
    obtain ⟨C, hlen, hC⟩ := hc (p s)
    exact hm₀ (p s) (by have := hbig s; omega) (by rw [hnu, hae]) (by rw [hnu, hpos]; exact hs) C hlen (sat_by_circuit hG hV hC hsat)
  -- one link of the chain
  have hlink : ∀ s, s < top a → (Sat (Phi (p s)) ↔ Sat (Phi (p (s + 1)))) := by
    intro s hs
    obtain ⟨hfit, htime⟩ := room (e := e) (L := p s) (P := p (s + 1)) (by have := hbig s; omega) (h3 s)
    have hPhi : Phi (p s) = tabF e (p s) (p (s + 1)) := by
      unfold Phi
      rw [hnu, hpos, hnext, hae, if_pos hs, if_pos hfit]
    rw [hPhi, he _ _ hfit]
    exact ⟨fun h => hsound _ _ h, fun h => (hacc (s + 1) hs h).mono (Nat.pow_le_pow_right (by norm_num) htime)⟩
  have hall : ∀ s, s ≤ top a → (Sat (Phi (p 0)) ↔ Sat (Phi (p s))) := by
    intro s
    induction s with
    | zero => intro _; exact Iff.rfl
    | succ s ih => intro hs; exact (ih (by omega)).trans (hlink s hs)
  -- the two ends
  have hp0 : p 0 = 2 ^ a := by rw [hp]; ring
  obtain ⟨hfit, htime⟩ := room (e := e) (L := 2 ^ a) (P := 2 ^ a) (by omega) (by omega)
  have hfirst : Sat (Phi (p 0)) ↔ Sat (tabF e (2 ^ a) (2 ^ a)) := by
    rw [he _ _ hfit]
    constructor
    · intro h
      have := hacc 0 (Nat.zero_le _) h
      rw [hp0] at this
      exact this.mono (Nat.pow_le_pow_right (by norm_num) htime)
    · intro h
      rw [hp0]
      exact hsound _ _ h
  have hlast : Sat (Phi (p (top a))) ↔ ¬Sat (tabF e (2 ^ a) (2 ^ a)) := by
    unfold Phi
    rw [hnu, hpos, hae, if_neg (lt_irrefl _), if_pos rfl]
    by_cases h : Sat (tabF e (2 ^ a) (2 ^ a))
    · rw [if_pos ⟨hfit, h⟩]
      exact ⟨fun h' => absurd h' not_sat_nil_clause, fun h' => absurd h h'⟩
    · rw [if_neg fun h' => h h'.2]
      exact ⟨fun _ => h, fun _ => sat_nil⟩
  have := (hall (top a) le_rfl).trans hlast
  rw [hfirst] at this
  exact (iff_not_self this)
end CircuitLowerBound
