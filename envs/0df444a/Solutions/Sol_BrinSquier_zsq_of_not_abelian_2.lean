-- Prove2me | solution 2 for BrinSquier.zsq_of_not_abelian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-13T20:34:44.722063+00:00
-- url     : https://prove2.me/submissions/c476f6a1-7f60-4404-a62d-eea8593bf68e

import Theorems.Thm_BrinSquier_freeAbelianBasis_infinite_of_not_abelian
import Definitions.Def_BrinSquier
import Mathlib

open BrinSquier

/-- The rank-two dichotomy as a corollary of the infinite-rank one: take the first two
members of the free abelian family. -/
theorem solution (G : Subgroup (ℝ ≃o ℝ))
    (hG : ∀ f ∈ G, IsPLFSlopeOne f) (hne : ¬ ∀ f ∈ G, ∀ g ∈ G, f * g = g * f) :
    ∃ u ∈ G, ∃ v ∈ G, u * v = v * u ∧
      Function.Injective (fun p : ℤ × ℤ => u ^ p.1 * v ^ p.2) := by
  obtain ⟨x, hxG, hxcomm, hxfree⟩ :=
    BrinSquier.freeAbelianBasis_infinite_of_not_abelian G hG hne
  refine ⟨x 0, hxG 0, x 1, hxG 1, hxcomm 0 1, ?_⟩
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  dsimp only at h
  -- the relation `x 0 ^ a * x 1 ^ b = x 0 ^ c * x 1 ^ d` becomes a trivial product
  have key : x 0 ^ (a - c) * x 1 ^ (b - d) = 1 := by
    have e : (x 0 ^ c)⁻¹ * (x 0 ^ a * x 1 ^ b) * (x 1 ^ d)⁻¹
        = (x 0 ^ c)⁻¹ * (x 0 ^ c * x 1 ^ d) * (x 1 ^ d)⁻¹ := by rw [h]
    calc x 0 ^ (a - c) * x 1 ^ (b - d)
        = (x 0 ^ c)⁻¹ * (x 0 ^ a * x 1 ^ b) * (x 1 ^ d)⁻¹ := by
          rw [zpow_sub, zpow_sub]; group
      _ = (x 0 ^ c)⁻¹ * (x 0 ^ c * x 1 ^ d) * (x 1 ^ d)⁻¹ := e
      _ = 1 := by group
  -- read it off the freeness condition at the duplicate-free list `[0, 1]`
  set n : ℤ → ℤ := fun m => if m = 0 then a - c else b - d with hn
  have hprod : (([0, 1] : List ℤ).map (fun m => x m ^ n m)).prod = 1 := by
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hn]
    norm_num
    exact key
  have h0 := hxfree [0, 1] (by decide) n hprod 0 (by simp)
  have h1 := hxfree [0, 1] (by decide) n hprod 1 (by simp)
  simp only [hn, if_pos rfl] at h0
  simp only [hn, if_neg (by decide : ¬(1 : ℤ) = 0)] at h1
  have : a = c := by omega
  have : b = d := by omega
  simp_all
