-- Prove2me | solution 1 for BrandSpillover.Commitment.quantity_game
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T04:20:39.88458+00:00
-- url     : https://prove2.me/submissions/a4024544-00f8-4e8c-a7c6-2ccd65b140a1

import Mathlib
import Definitions.Def_BrandSpillover_Commitment_Model

open BrandSpillover.Commitment SupplierAudit.Competition

theorem solution (θW kS kW : ℝ) :
    IsQuantityNE θW kS kW (focQS θW kS kW) (focQW θW kS kW) ∧
    (∀ x y : ℝ, IsQuantityNE θW kS kW x y → x = focQS θW kS kW ∧ y = focQW θW kS kW) ∧
    SupplierAudit.Competition.cournotPayoff 1 1 kS (focQS θW kS kW) (focQW θW kS kW) =
      focQS θW kS kW ^ 2 ∧
    SupplierAudit.Competition.cournotPayoff 1 θW kW (focQW θW kS kW) (focQS θW kS kW) =
      focQW θW kS kW ^ 2 := by
  -- best-response identities: payoff(x) - payoff(x') = (x - x')^2 when x is the best response
  have brS : ∀ y x' : ℝ, cournotPayoff 1 1 kS ((1 - y - kS)/2) y - cournotPayoff 1 1 kS x' y
      = (x' - (1 - y - kS)/2)^2 := by
    intro y x'; unfold cournotPayoff; ring
  have brW : ∀ x y' : ℝ, cournotPayoff 1 θW kW ((θW - x - kW)/2) x - cournotPayoff 1 θW kW y' x
      = (y' - (θW - x - kW)/2)^2 := by
    intro x y'; unfold cournotPayoff; ring
  have hx : focQS θW kS kW = (1 - focQW θW kS kW - kS)/2 := by unfold focQS focQW; ring
  have hy : focQW θW kS kW = (θW - focQS θW kS kW - kW)/2 := by unfold focQS focQW; ring
  refine ⟨⟨fun x' => ?_, fun y' => ?_⟩, fun x y h => ?_, ?_, ?_⟩
  · have := brS (focQW θW kS kW) x'
    rw [← hx] at this; nlinarith [sq_nonneg (x' - focQS θW kS kW)]
  · have := brW (focQS θW kS kW) y'
    rw [← hy] at this; nlinarith [sq_nonneg (y' - focQW θW kS kW)]
  · obtain ⟨h1, h2⟩ := h
    have e1 := brS y x
    have e2 := brW x y
    have k1 := h1 ((1 - y - kS)/2)
    have k2 := h2 ((θW - x - kW)/2)
    have s1 : (x - (1 - y - kS)/2)^2 ≤ 0 := by linarith
    have s2 : (y - (θW - x - kW)/2)^2 ≤ 0 := by linarith
    have t1 : x - (1 - y - kS)/2 = 0 := by nlinarith [sq_nonneg (x - (1 - y - kS)/2)]
    have t2 : y - (θW - x - kW)/2 = 0 := by nlinarith [sq_nonneg (y - (θW - x - kW)/2)]
    unfold focQS focQW
    constructor <;> linarith
  · unfold cournotPayoff focQS focQW; ring
  · unfold cournotPayoff focQS focQW; ring
