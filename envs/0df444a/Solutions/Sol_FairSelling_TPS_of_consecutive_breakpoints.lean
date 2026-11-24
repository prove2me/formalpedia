-- Prove2me | solution 1 for FairSelling.TPS_of_consecutive_breakpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:37:40.017801+00:00
-- url     : https://prove2.me/submissions/ad8911ff-e70f-44bc-9251-c39ebd991322

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Theorems.Thm_FairSelling_TPS_eq_bracket_formula
import Theorems.Thm_FairSelling_vval_mem_breakpoints
import Theorems.Thm_FairSelling_price_mem_breakpoints

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hn : 0 < n) (hp : ∀ g, 0 ≤ p g)
    {a c : ℝ} (hac : a < c) (hc : c ∈ breakpoints v p)
    (hgap : ∀ s ∈ breakpoints v p, s ≤ a ∨ c ≤ s)
    (hfa : a ≤ truncSum n v p a)
    (habove : ∀ s ∈ breakpoints v p, c ≤ s → truncSum n v p s < s) :
    ((slopeGoods v p a c).card : ℝ) < n ∧
      TPS n v p = flatConst v p a c / (n - ((slopeGoods v p a c).card : ℝ)) ∧
      a ≤ TPS n v p ∧ TPS n v p < c := by
  refine TPS_eq_bracket_formula v p hn hp (le_of_lt hac)
    (fun g => ⟨hgap _ (vval_mem_breakpoints v p g), hgap _ (price_mem_breakpoints v p g)⟩)
    hfa (habove c hc (le_refl c))
    (fun g hg => habove _ (vval_mem_breakpoints v p g) hg)
    (fun g hg => habove _ (price_mem_breakpoints v p g) hg)
end FairSelling
