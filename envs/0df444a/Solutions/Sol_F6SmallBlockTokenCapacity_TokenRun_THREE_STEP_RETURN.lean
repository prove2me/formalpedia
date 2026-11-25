-- Prove2me | solution 1 for F6SmallBlockTokenCapacity.TokenRun.THREE_STEP_RETURN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:42:24.365807+00:00
-- url     : https://prove2.me/submissions/faa968fc-02b9-46cb-bb94-e94534c87a9a

import Mathlib
import Definitions.Def_StableMarriageF6_F6SmallBlockTokenCapacity
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_mem_participationSteps
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_named_pair_swap
import Theorems.Thm_F6SmallBlockTokenCapacity_TokenRun_triangle_supports
attribute [local simp] F6SmallBlockTokenCapacity.TokenRun.mem_participationSteps

set_option autoImplicit true
open scoped BigOperators
open Classical
noncomputable section
open F6SmallBlockTokenCapacity
variable {B W : Type*} [Fintype B] [Fintype W] {q : ℕ}
open F6SmallBlockTokenCapacity.TokenRun
variable (R : TokenRun B W q)
namespace F6SmallBlockTokenCapacity.TokenRun
theorem _root_.solution (P : TokenRun B W 3)
    (hB : Fintype.card B = 3)
    (hs : ∀ i, (P.support i).card = 2)
    (hc : ∀ b : B, (P.participationSteps b).card = 2) :
    ∃ x : B, x ∈ P.support 0 ∧ x ∉ P.support 1 ∧ x ∈ P.support 2 ∧
      P.state 3 x = P.state 0 x := by
  classical
  obtain ⟨x, a, b, hxa, hxb, hab, h0, h1, h2⟩ :=
    triangle_supports P.support hB hs (by simpa [participationSteps] using hc)
  have hswap0 := P.named_pair_swap 0 x a hxa h0
  have hswap1 := P.named_pair_swap 1 a b hab h1
  have hswap2 := P.named_pair_swap 2 x b hxb h2
  refine ⟨x, by simp [h0], by simp [h1, hxa, hxb], by simp [h2], ?_⟩
  calc
    P.state 3 x = P.state 2 b := hswap2.1
    _ = P.state 1 a := hswap1.2
    _ = P.state 0 x := hswap0.2
end F6SmallBlockTokenCapacity.TokenRun
