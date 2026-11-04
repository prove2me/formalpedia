-- Prove2me | solution 1 for ChainCompSI.Backfire.proposition_1_i
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T08:25:42.477812+00:00
-- url     : https://prove2.me/submissions/a3f4b3aa-80c5-43a9-b13e-7db16a91a97c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_ChainCompSI_Backfire_table_1_ni
import Theorems.Thm_ChainCompSI_Backfire_table_1_si

open ChainCompSI.Backfire

theorem solution (θ h : ℝ) (hθ : 0 < θ) (hh : 0 ≤ h) : (∃ E, IsEq θ h SI E) ∧ ∀ E, IsEq θ h SI E → ∀ i : Fin 2, (0 < E.inv i ↔ h < 1 / (4 + θ)) := by
  have h4 : (0 : ℝ) < 4 + θ := by linarith
  have hiff : h < 1 / (4 + θ) ↔ h * (4 + θ) < 1 := lt_div_iff₀ h4
  rcases le_or_gt (h * (4 + θ)) 1 with hle | hgt
  · obtain ⟨ex, hall⟩ := table_1_si θ h hθ hh hle
    refine ⟨ex, fun E hE i => ?_⟩
    rw [(hall E hE i).2.2.2.1, hiff]
    have hK : 0 < (1 + θ) * (20 + 7 * θ) / ((2 + θ) * (68 + 19 * θ)) := by positivity
    have e : (1 + θ) * (20 + 7 * θ) * (1 - h * (4 + θ)) / ((2 + θ) * (68 + 19 * θ)) =
        (1 + θ) * (20 + 7 * θ) / ((2 + θ) * (68 + 19 * θ)) * (1 - h * (4 + θ)) := by ring
    rw [e]
    constructor
    · intro hp
      have := (pos_iff_pos_of_mul_pos hp).1 hK
      linarith
    · intro hx
      exact mul_pos hK (by linarith)
  · obtain ⟨ex, hall⟩ := table_1_ni θ h hθ hh SI (Or.inr ⟨rfl, hgt⟩)
    refine ⟨ex, fun E hE i => ?_⟩
    rw [(hall E hE i).2.2.2.1, hiff]
    constructor <;> intro hc <;> linarith
