-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.corollary_4_19
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T19:04:32.646131+00:00
-- url     : https://prove2.me/submissions/78f2d1e9-9bd8-44ec-9494-3795c09a5a30

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Theorems.Thm_BinaryExtForm_HypercubeRank_lemma_4_18

set_option autoImplicit false

namespace BinaryExtForm.HypercubeRank

lemma hit_ncard_eq_dim_sub_fB {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ))
    (α : Fin ℓ → ℕ) : Set.ncard {i : Fin d | typeHit B α i} = d - fB B α := by
  classical
  have hsum := Set.ncard_add_ncard_compl {i : Fin d | typeHit B α i}
  have hc : Set.ncard ({i : Fin d | typeHit B α i}ᶜ) = fB B α := by
    unfold fB
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp
  rw [hc] at hsum
  simp only [Nat.card_fin] at hsum
  omega

end BinaryExtForm.HypercubeRank

open BinaryExtForm.HypercubeRank

theorem solution {d ℓ : ℕ} (B : Set (Fin (d + 1) → ℝ)) (hB : IsHypercubeBinarization d B)
    (α : Fin ℓ → ℕ) (hα : ∀ j, α j + 2 ≤ 2 ^ d)
    (xbar : Fin ℓ → ℝ) (hx : ∀ j, (α j : ℝ) < xbar j ∧ xbar j < α j + 1) :
    rk B xbar = d - fB B α := by
  rw [lemma_4_18 B hB α hα xbar hx, hit_ncard_eq_dim_sub_fB]
