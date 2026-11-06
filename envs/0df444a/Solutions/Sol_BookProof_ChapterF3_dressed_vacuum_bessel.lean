-- Prove2me | solution 1 for BookProof.ChapterF3.dressed_vacuum_bessel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T13:18:52.754764+00:00
-- url     : https://prove2.me/submissions/f9acf6fd-18be-4fc1-a715-433afd32484e

-- Generated from ChapterF3.lean — solution of BookProof.ChapterF3.dressed_vacuum_bessel
import Mathlib
import Definitions.Def_ChapterF3
open BookProof.ChapterF3



open scoped BigOperators
open Polynomial


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']

set_option maxHeartbeats 1000000 in

theorem solution {ι : Type*} (x : ι → E') (hx : Orthonormal ℂ x)
    (v : E') (hv : ‖v‖ = 1) (s : Finset ι) :
    ∑ j ∈ s, ‖inner (𝕜 := ℂ) (x j) v‖ ^ 2 ≤ 1 := by
  convert hx.sum_inner_products_le v using 1;
  rw [ hv, one_pow ]

/-! ## F2.9 — the Mehler projector as the off-diagonal generator -/

/-
**F2.9**: the channel matrix elements of the vacuum projector
`H₀ = |v⟩⟨v|` are `⟪xᵢ, H₀ xⱼ⟫ = conj(⟪v, xᵢ⟫) · ⟪v, xⱼ⟫ = conj εᵢ · εⱼ`
(with `εₖ = ⟪v, xₖ⟫`).  A one-line corollary of F2.6: the projector is by itself
an off-diagonal generator.
-/
