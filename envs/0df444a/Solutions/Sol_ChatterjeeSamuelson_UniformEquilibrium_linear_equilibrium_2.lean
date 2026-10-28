-- Prove2me | solution 2 for ChatterjeeSamuelson.UniformEquilibrium.linear_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:41.966761+00:00
-- url     : https://prove2.me/submissions/30dd4dc4-9a5a-4361-b7ed-2c50cad6e719

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_Shared_unif
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerLinear
import Definitions.Def_ChatterjeeSamuelson_Shared_buyerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_sellerProfit
import Definitions.Def_ChatterjeeSamuelson_Shared_IsEquilibrium
import Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_buyer_best_response
import Theorems.Thm_ChatterjeeSamuelson_UniformEquilibrium_seller_best_response

-- carved verbatim out of submission 6b738584-921f-4716-afd8-a1a80395f217, lines 411-420

section
open MeasureTheory ProbabilityTheory Set
open ChatterjeeSamuelson

theorem solution (k vbar : ℝ) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hvbar : 0 < vbar)
    (S B : ℝ → ℝ) (hSmeas : Measurable S) (hBmeas : Measurable B)
    (hS_eq : ∀ v, 0 ≤ v → v ≤ (2 - k) / 2 * vbar → S v = Shared.sellerLinear k vbar v)
    (hS_ge : ∀ v, (2 - k) / 2 * vbar < v → v ≤ vbar → Shared.sellerLinear k vbar v ≤ S v)
    (hB_le : ∀ v, 0 ≤ v → v < (1 - k) / 2 * vbar → B v ≤ Shared.buyerLinear k vbar v)
    (hB_eq : ∀ v, (1 - k) / 2 * vbar ≤ v → v ≤ vbar → B v = Shared.buyerLinear k vbar v) :
    Shared.IsEquilibrium k (Shared.unif vbar) (Shared.unif vbar) 0 vbar 0 vbar S B := by
  exact ⟨ChatterjeeSamuelson.UniformEquilibrium.buyer_best_response k vbar hk0 hk1 hvbar S B hSmeas hBmeas hS_eq hS_ge hB_le hB_eq,
    ChatterjeeSamuelson.UniformEquilibrium.seller_best_response k vbar hk0 hk1 hvbar S B hSmeas hBmeas hS_eq hS_ge hB_le hB_eq⟩

end
