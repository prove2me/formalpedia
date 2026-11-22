-- Prove2me | solution 1 for Egrs75.SeedWindow.walk_hits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:04.277184+00:00
-- url     : https://prove2.me/submissions/408d821f-2122-4d71-b35f-6a576be8f0c3

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Definitions.Def_LeanPool_Egrs75_SeedWindow

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.SeedWindow
open Nat
open Egrs75
namespace Egrs75.SeedWindow
theorem _root_.solution {δ w₁ w₂ start : ℝ} (hδ0 : 0 < δ) (hδw : δ < w₂ - w₁)
    (hstart : start < w₁) :
    ∃ t : ℕ, 1 ≤ t ∧ w₁ < start + t * δ ∧ start + t * δ < w₂ := by
  classical
  have hex : ∃ T : ℕ, w₁ < start + T * δ := by
    obtain ⟨T, hT⟩ := exists_nat_gt ((w₁ - start) / δ)
    refine ⟨T, ?_⟩
    have := (div_lt_iff₀ hδ0).mp hT
    linarith
  have ht : w₁ < start + (Nat.find hex : ℝ) * δ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht1 : 1 ≤ t := by
    by_contra h
    have h0 : t = 0 := by omega
    rw [h0] at ht
    push_cast at ht
    linarith
  have hprev : ¬ w₁ < start + ((t - 1 : ℕ) : ℝ) * δ := by
    rw [htdef]
    exact Nat.find_min hex (by omega)
  push Not at hprev
  have hcast : ((t : ℕ) : ℝ) = ((t - 1 : ℕ) : ℝ) + 1 := by
    simp_all
  refine ⟨t, ht1, ht, ?_⟩
  have hstep : start + (t : ℝ) * δ = (start + ((t - 1 : ℕ) : ℝ) * δ) + δ := by
    rw [hcast]; ring
  rw [hstep]
  linarith
end Egrs75.SeedWindow
