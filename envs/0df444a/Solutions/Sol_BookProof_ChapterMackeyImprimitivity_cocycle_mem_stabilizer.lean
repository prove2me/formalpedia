-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T14:13:07.120235+00:00
-- url     : https://prove2.me/submissions/b7e3af82-1012-406d-81d2-d66a931341b3

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.cocycle_mem_stabilizer
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_inv_smul_section
open BookProof.ChapterMackeyImprimitivity



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution (hs : ∀ x, s x • x₀ = x) (g : G) (x : X) :
    cocycle s g x ∈ MulAction.stabilizer G x₀ := by

  change cocycle s g x • x₀ = x₀
  rw [cocycle, mul_smul, mul_smul, hs (g⁻¹ • x), smul_inv_smul, inv_smul_section hs x]
