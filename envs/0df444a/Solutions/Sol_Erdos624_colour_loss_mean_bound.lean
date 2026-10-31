-- Prove2me | solution 1 for Erdos624.colour_loss_mean_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:11:05.359528+00:00
-- url     : https://prove2.me/submissions/fe4acc06-4256-42d2-b72e-fa6fe8944bcf

import Mathlib
open Finset
namespace E624R17C
open Finset

/-- (C) Exact capacity decomposition on ℕ:
`cap - minimal = (cap - raw) + (raw - newRaw) + (newRaw - minimal)`
when `minimal ≤ newRaw ≤ raw ≤ cap`. -/
theorem clipping_capacity_decomposition
    (cap raw newRaw minimal : ℕ)
    (h1 : minimal ≤ newRaw) (h2 : newRaw ≤ raw) (h3 : raw ≤ cap) :
    cap - minimal = (cap - raw) + (raw - newRaw) + (newRaw - minimal) := by
  omega

/-- (L) Colour-loss averaging: pointwise `ℓ ≤ d` and `∑ d ≤ (E+c)·|ι|` imply the same for `ℓ`. -/
theorem colour_loss_mean_bound {α : Type*} [Fintype α]
    (ℓ d : α → ℝ) (E c : ℝ)
    (hℓ : ∀ a, ℓ a ≤ d a)
    (hd : ∑ a : α, d a ≤ (E + c) * Fintype.card α) :
    ∑ a : α, ℓ a ≤ (E + c) * Fintype.card α :=
  le_trans (sum_le_sum fun a _ => hℓ a) hd

/-- (G-core) Each marked `k`-set contributes exactly `2^k - 1` nonempty subsets;
summing over a family `B ⊆ powersetCard k P` yields `#B * (2^k - 1)`. -/
theorem shadow_footprint_lower {α : Type*} [DecidableEq α]
    (P : Finset α) (k : ℕ) (B : Finset (Finset α))
    (hB : B ⊆ P.powersetCard k) :
    ∑ Y ∈ B, (2 ^ #Y - 1) = #B * (2 ^ k - 1) := by
  classical
  have hY : ∀ Y ∈ B, #Y = k := fun Y hY => (mem_powersetCard.1 (hB hY)).2
  calc ∑ Y ∈ B, (2 ^ #Y - 1)
      = ∑ Y ∈ B, (2 ^ k - 1) := by
          apply sum_congr rfl
          intro Y hYmem; rw [hY Y hYmem]
    _ = #B * (2 ^ k - 1) := by simp [sum_const]

end E624R17C

namespace Erdos624

theorem colour_loss_mean_bound {α : Type*} [Fintype α]
    (ℓ d : α → ℝ) (E c : ℝ)
    (hℓ : ∀ a, ℓ a ≤ d a)
    (hd : ∑ a : α, d a ≤ (E + c) * Fintype.card α) :
    ∑ a : α, ℓ a ≤ (E + c) * Fintype.card α := by
  exact E624R17C.colour_loss_mean_bound ℓ d E c hℓ hd

end Erdos624

open Finset

theorem solution {α : Type*} [Fintype α]
    (ℓ d : α → ℝ) (E c : ℝ)
    (hℓ : ∀ a, ℓ a ≤ d a)
    (hd : ∑ a : α, d a ≤ (E + c) * Fintype.card α) :
    ∑ a : α, ℓ a ≤ (E + c) * Fintype.card α :=
  Erdos624.colour_loss_mean_bound ℓ d E c hℓ hd
