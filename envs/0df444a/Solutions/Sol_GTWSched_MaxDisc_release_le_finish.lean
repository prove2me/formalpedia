-- Prove2me | solution 1 for GTWSched.MaxDisc.release_le_finish
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T04:21:54.380025+00:00
-- url     : https://prove2.me/submissions/72d1682c-fe22-4552-8def-fd48a7ac7627

import Mathlib
import Definitions.Def_GTWSched_MaxDisc_Model



namespace GTWSched.MaxDisc

theorem rle_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) :
    ∀ i, σ.symm n < σ.symm i → r i ≤ s n + l n := by
  intro i _
  obtain ⟨_, hF⟩ := hS
  have hn1 := hF n
  have hn2 := hn i
  have hr0 := hr n
  have hli := hl i
  have hln := hl n
  have hi := hr i
  rcases hsf i with h | ⟨h0, h1⟩
  · rcases hsf n with h' | ⟨h0', h1'⟩
    · linarith [hn1.1, hn1.2]
    · linarith [hn1.1, hn1.2]
  · linarith [hn1.1]

theorem rtp_core {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) (hrtp : ReleaseTimeProperty r σ s n) :
    ∀ i, i ≠ n → (σ.symm i < σ.symm n ↔ d i ≤ s n + α) := by
  intro i hin
  obtain ⟨hO, hF⟩ := hS
  have hne : σ.symm i ≠ σ.symm n := fun h => hin (σ.symm.injective h)
  constructor
  · intro h
    have h1 := hO _ _ h
    simp only [Equiv.apply_symm_apply] at h1
    have := hF i
    have := hr i
    have := hl i
    rcases hsf i with h | ⟨h0, h1'⟩ <;> linarith [(hF i).1]
  · intro h
    by_contra hc
    have hgt : σ.symm n < σ.symm i := lt_of_le_of_ne (not_lt.mp hc) (Ne.symm hne)
    have := hrtp i hgt
    have := hl i
    have := hr n
    have := (hF n).1
    rcases hsf i with h' | ⟨h0, h1'⟩ <;> linarith

end GTWSched.MaxDisc

open GTWSched.MaxDisc


theorem solution {N : ℕ} (r d l : Fin N → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hr : ∀ i, 0 ≤ r i) (hl : ∀ i, 0 ≤ l i) (hsf : SpecialForm r d l α)
    (n : Fin N) (hn : ∀ i, d i ≤ d n) (σ : Fin N ≃ Fin N) (s : Fin N → ℝ)
    (hS : Feasible r d l σ s) :
    ∀ i, σ.symm n < σ.symm i → r i ≤ s n + l n := by
  exact rle_core r d l α hα hr hl hsf n hn σ s hS
