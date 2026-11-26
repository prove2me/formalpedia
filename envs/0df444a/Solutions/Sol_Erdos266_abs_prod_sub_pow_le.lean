-- Prove2me | solution 1 for Erdos266.abs_prod_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:30.568751+00:00
-- url     : https://prove2.me/submissions/221a0f78-4d42-4ca5-9d4b-3e2563303081

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {ι : Type*} {s : Finset ι} {c : ι → ℝ} {N B : ℝ}
    (_hB : 0 ≤ B) (hBN : B ≤ N) (hN : 0 < N) (hc : ∀ j ∈ s, |c j| ≤ B) :
    |(∏ j ∈ s, (N + c j)) - N ^ s.card|
      ≤ (2 ^ s.card - 1) * B * N ^ s.card / N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have hca : |c a| ≤ B := hc a (mem_insert_self a s)
    have hprev := ih fun j hj => hc j (mem_insert_of_mem hj)
    rw [prod_insert ha, card_insert_of_notMem ha]
    have hNa : |N + c a| ≤ 2 * N := by
      rw [abs_le] at hca ⊢
      constructor <;> nlinarith
    have hiden : (N + c a) * (∏ j ∈ s, (N + c j)) - N ^ (s.card + 1)
        = (N + c a) * ((∏ j ∈ s, (N + c j)) - N ^ s.card) + c a * N ^ s.card := by
      ring
    rw [hiden]
    calc |(N + c a) * ((∏ j ∈ s, (N + c j)) - N ^ s.card) + c a * N ^ s.card|
        ≤ |N + c a| * |(∏ j ∈ s, (N + c j)) - N ^ s.card| + |c a| * N ^ s.card := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_pow, abs_of_pos hN]
    _ ≤ (2 * N) * ((2 ^ s.card - 1) * B * N ^ s.card / N) + B * N ^ s.card := by
          gcongr
    _ = (2 ^ (s.card + 1) - 1) * B * N ^ (s.card + 1) / N := by
          field_simp
          ring
end Erdos266
