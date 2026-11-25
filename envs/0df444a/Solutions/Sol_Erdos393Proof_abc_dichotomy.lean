-- Prove2me | solution 1 for Erdos393Proof.abc_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:32:25.542805+00:00
-- url     : https://prove2.me/submissions/e205db3c-93b8-478c-badd-81c78d9e7159

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (habc : AbcHyp) (ε : ℝ) (hε : 0 < ε) :
    ∃ cmax : ℕ, ∀ u v w : ℕ, 0 < u → 0 < v → Nat.Coprime u v → u + v = w →
      w ≤ cmax ∨ (w : ℝ) ≤ (radical (u * v * w) : ℝ) ^ (1 + ε) := by
  obtain ⟨cmax, hc⟩ := ((habc ε hε).image fun t : ℕ × ℕ × ℕ ↦ t.2.2).bddAbove
  refine ⟨cmax, fun u v w hu hv huv huvw ↦ ?_⟩
  by_cases h : (radical (u * v * w) : ℝ) ^ (1 + ε) < w
  · left
    have huw : Nat.Coprime u w := by
      rw [← huvw, add_comm]; exact Nat.coprime_add_self_right.2 huv
    have hvw : Nat.Coprime v w := by
      rw [← huvw]; exact Nat.coprime_add_self_right.2 huv.symm
    have hvu := huv.symm
    have hwu := huw.symm
    have hwv := hvw.symm
    refine hc ⟨(u, v, w), ⟨hu, hv, show 0 < w by omega, ?_, huvw, h⟩, rfl⟩
    show ({u, v, w} : Set ℕ).Pairwise Nat.Coprime
    rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) hxy <;>
      first | exact absurd rfl hxy | assumption
  · exact Or.inr (not_lt.1 h)
end Erdos393Proof
