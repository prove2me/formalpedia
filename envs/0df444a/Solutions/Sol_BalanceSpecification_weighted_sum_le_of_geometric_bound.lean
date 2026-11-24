-- Prove2me | solution 1 for BalanceSpecification.weighted_sum_le_of_geometric_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:09.449988+00:00
-- url     : https://prove2.me/submissions/37e6078c-a055-4578-a3bd-951517476efb

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_RenewalBounds

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution
    {b : ℕ → ℝ} {θ ρ C : ℝ} (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hθρ : θ < ρ)
    (hC : 0 ≤ C) (hb : ∀ l : ℕ, b l ≤ C * θ ^ l) (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) ≤ C / (1 - θ / ρ) := by
  have hr : 0 ≤ θ / ρ := div_nonneg hθ hρ.le
  have hr1 : θ / ρ < 1 := (div_lt_one hρ).mpr hθρ
  have hgeom : (∑ l ∈ Finset.range (n + 1), (θ / ρ) ^ l) ≤ 1 / (1 - θ / ρ) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    rw [geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg hr _)
  calc
    (∑ l ∈ Finset.range (n + 1), b l / ρ ^ l) ≤
        ∑ l ∈ Finset.range (n + 1), (C * θ ^ l) / ρ ^ l :=
      Finset.sum_le_sum (fun l _ => div_le_div_of_nonneg_right (hb l) (pow_nonneg hρ.le l))
    _ = C * (∑ l ∈ Finset.range (n + 1), (θ / ρ) ^ l) := by
      simp only [div_pow, mul_div_assoc, Finset.mul_sum]
    _ ≤ C * (1 / (1 - θ / ρ)) := mul_le_mul_of_nonneg_left hgeom hC
    _ = C / (1 - θ / ρ) := by ring
end BalanceSpecification
