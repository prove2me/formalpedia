-- Prove2me | solution 1 for CompOT.DualAscent.proposition_3_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-13T21:31:14.349214+00:00
-- url     : https://prove2.me/submissions/30b74fc0-e26d-45b9-af3f-e888e90d8519

import Mathlib
import Definitions.Def_CompOT_DualAscent_Defs
import Theorems.Thm_CompOT_DualAscent_proposition_3_3
import Theorems.Thm_CompOT_DualAscent_proposition_3_5
import Theorems.Thm_CompOT_DualAscent_prop_3_6_objective_change
import Theorems.Thm_CompOT_DualAscent_prop_3_6_labeling

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : CompOT.Duality.dualFeasible C f g) :
    CompOT.Duality.IsDualOptimal C a b f g ∨
      ∃ (S : Finset (Fin n)) (S' : Finset (Fin m)) (ε₀ : ℝ), 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          CompOT.Duality.dualFeasible C (f + ε • CompOT.DualAscent.indicatorVec S)
              (g - ε • CompOT.DualAscent.indicatorVec S') ∧
          CompOT.Duality.dualObj a b f g <
            CompOT.Duality.dualObj a b (f + ε • CompOT.DualAscent.indicatorVec S)
              (g - ε • CompOT.DualAscent.indicatorVec S') := by
  classical
  by_cases h : ∃ P ∈ CompOT.Assignment.couplings a b, CompOT.Duality.Complementary C P f g
  · obtain ⟨P, hP, hc⟩ := h
    exact Or.inl (CompOT.DualAscent.proposition_3_3 C a b P f g hP hfg hc).2
  · obtain ⟨S, S', hS, hpos⟩ := CompOT.DualAscent.prop_3_6_labeling C a b ha hb f g hfg h
    obtain ⟨ε₀, hε₀, hfeas⟩ := CompOT.DualAscent.proposition_3_5 C f g hfg S S' hS
    refine Or.inr ⟨S, S', ε₀, hε₀, fun ε hε hεε₀ => ⟨hfeas ε hε hεε₀, ?_⟩⟩
    have hchg := CompOT.DualAscent.prop_3_6_objective_change a b f g S S' ε
    have := mul_pos hε hpos
    linarith
