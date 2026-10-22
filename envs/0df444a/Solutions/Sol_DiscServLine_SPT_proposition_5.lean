-- Prove2me | solution 1 for DiscServLine.SPT.proposition_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:44:11.435019+00:00
-- url     : https://prove2.me/submissions/ca0a93ee-1aac-47b8-a548-e1bc99a275c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model
import Theorems.Thm_DiscServLine_SPT_proposition_5_i_ii
import Theorems.Thm_DiscServLine_SPT_proposition_5_iii_top
import Theorems.Thm_DiscServLine_SPT_proposition_5_iii_bottom

open DiscServLine.SPT

theorem solution (θbar b c : ℝ) (hc : 0 < c) (hcθ : c < θbar) (hb : 0 < b) :
    (∀ Λ : ℝ, 0 < Λ →
      (∃ d, IsOptimal ⟨θbar, b, c, Λ⟩ d) ∧
      ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        d.lo < d.hi ∧ d.Λk 0 = Λ ∧
        ConcaveOn ℝ (Set.Icc d.lo d.hi) (price ⟨θbar, b, c, Λ⟩ d) ∧
        ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.hi) ∧
    ∃ Λlow Λhigh : ℝ, 0 < Λlow ∧ 0 < Λhigh ∧
      (∀ Λ ∈ Set.Ioo 0 Λlow, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        ∃ p < 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) ∧
      (∀ Λ ∈ Set.Ioi Λhigh, ∀ d, IsOptimal ⟨θbar, b, c, Λ⟩ d →
        ∃ p > 0, HasDerivWithinAt (price ⟨θbar, b, c, Λ⟩ d) p (Set.Icc d.lo d.hi) d.lo) := by
  refine ⟨fun Λ hΛ => ?_, (proposition_5_iii_bottom θbar b c hc hcθ hb).2⟩
  have hP : Params.Standing ⟨θbar, b, c, Λ⟩ := ⟨hc, hcθ, hb, hΛ⟩
  obtain ⟨hex, h12⟩ := proposition_5_i_ii _ hP
  obtain ⟨-, h3⟩ := proposition_5_iii_top _ hP
  refine ⟨hex, fun d hd => ?_⟩
  obtain ⟨a1, a2⟩ := h12 d hd
  exact ⟨a1, a2, h3 d hd⟩
