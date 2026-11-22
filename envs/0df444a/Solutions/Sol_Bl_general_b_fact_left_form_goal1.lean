-- Prove2me | solution 1 for Bl.general_b_fact_left_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:41.795959+00:00
-- url     : https://prove2.me/submissions/72d0890f-566a-492b-9686-f2a516e5501e

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
universe u v w
open Bl Bl.general_b_fact_left_form
namespace Bl.general_b_fact_left_form
theorem _root_.solution {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) (θ : ℝ) (j : Fin n) :
    θ ≤ f j ↔ (j : ℕ) < (Finset.univ.filter (fun i => θ ≤ f i)).card := by
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => θ ≤ f i) := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_trans h (hf hi)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hn0
    have hn := not_le.mp hn0
    have hsub : Finset.univ.filter (fun i => θ ≤ f i) ⊆ Finset.Iio j := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Iio]
      by_contra hji0
      have hji := not_lt.mp hji0
      exact absurd (lt_of_le_of_lt (hf hji) hn) (not_lt.mpr hi.2)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
end Bl.general_b_fact_left_form
