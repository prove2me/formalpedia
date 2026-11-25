-- Prove2me | solution 1 for ErdosGirth.sum_cycle_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:28.775745+00:00
-- url     : https://prove2.me/submissions/d58b7a10-0e68-4b99-9971-31425264c0f8

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux
public import Theorems.Thm_ErdosGirth_sum_card_closed_walks

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (ℓ : ℕ) :
    ∑ u : Fin m, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
      (if c.IsCycle then p ^ ℓ else 0) ≤ ((m : ℝ) * p) ^ ℓ := by
  cases ℓ with
  | zero =>
    rw [sum_eq_zero]
    · positivity
    intro u _
    refine sum_eq_zero fun c hc => ?_
    rw [ite_eq_right_iff]
    intro hcyc
    have := hcyc.three_le_length
    rw [mem_finsetWalkLength_iff.mp hc] at this
    omega
  | succ n =>
    calc _ ≤ ∑ u : Fin m, ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength (n + 1) u u,
          p ^ (n + 1) :=
          sum_le_sum fun u _ => sum_le_sum fun c _ => by
            split_ifs <;> first | exact le_rfl | positivity
      _ = (∑ u : Fin m, #((⊤ : SimpleGraph (Fin m)).finsetWalkLength (n + 1) u u) : ℕ)
          * p ^ (n + 1) := by
          simp [sum_mul]
      _ ≤ ((m ^ (n + 1) : ℕ) : ℝ) * p ^ (n + 1) := by
          gcongr
          simpa using sum_card_closed_walks (⊤ : SimpleGraph (Fin m)) n
      _ = ((m : ℝ) * p) ^ (n + 1) := by push_cast; ring
end ErdosGirth
