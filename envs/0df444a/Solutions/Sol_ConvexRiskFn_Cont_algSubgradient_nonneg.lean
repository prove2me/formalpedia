-- Prove2me | solution 1 for ConvexRiskFn.Cont.algSubgradient_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T03:55:37.673247+00:00
-- url     : https://prove2.me/submissions/4b2cdcc1-ba13-4e73-8922-30cc904b7d01

import Definitions.Def_ConvexRiskFn_Cont_Setting
set_option autoImplicit false
open ConvexRiskFn.Cont Filter Topology

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] (ρ : E → EReal) (h2 : A2 ρ) (Xbar : E)
    (hdom : Xbar ∈ ConvexRiskFn.Dual.dom ρ) (hbot : ⊥ < ρ Xbar) (l : E →ₗ[ℝ] ℝ)
    (hl : IsAlgSubgradient ρ Xbar l) :
    ∀ X : E, 0 ≤ X → 0 ≤ l X := by
  intro X hX
  have hle : Xbar-X ≤ Xbar := sub_le_self Xbar hX
  have hm := h2 (Xbar-X) Xbar hle
  have hs := (hl (Xbar-X)).trans hm
  have he : Xbar-X-Xbar = -X := by abel
  rw [he,map_neg] at hs
  have hfin : ρ Xbar ≠ ⊤ := ne_of_lt (show ρ Xbar < ⊤ from hdom)
  have hnbot : ρ Xbar ≠ ⊥ := ne_of_gt hbot
  have hc : ρ Xbar=(((ρ Xbar).toReal:ℝ):EReal) := (EReal.coe_toReal hfin hnbot).symm
  rw [hc,← EReal.coe_add,EReal.coe_le_coe_iff] at hs
  linarith


#print axioms solution

open ConvexRiskFn.Cont Filter Topology
namespace ConvexRiskFn.Cont

example {E : Type*} [AddCommGroup E] [Module ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] (ρ : E → EReal) (h2 : A2 ρ) (Xbar : E)
    (hdom : Xbar ∈ ConvexRiskFn.Dual.dom ρ) (hbot : ⊥ < ρ Xbar) (l : E →ₗ[ℝ] ℝ)
    (hl : IsAlgSubgradient ρ Xbar l) :
    ∀ X : E, 0 ≤ X → 0 ≤ l X := by
  exact solution ρ h2 Xbar hdom hbot l hl

end ConvexRiskFn.Cont

#print axioms solution
