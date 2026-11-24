-- Prove2me | solution 1 for BalanceSpecification.marker_suffixLength_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:52.70699+00:00
-- url     : https://prove2.me/submissions/18fab53b-98e0-44a2-88e7-e3396c475062

module
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter
open scoped Topology
open BalanceSpecification
namespace BalanceSpecification
theorem _root_.solution {s : ℕ → ℕ} {M : ℕ}
    (hpos : ∀ n, 0 < s n) (hgap : ∀ n, 2 * s n < s (n + 1))
    (hlow : ∀ n, n + M ≤ s n) : StrictMono (fun n => s n - n - M) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hp := hpos n
  have hg := hgap n
  have hl := hlow n
  have hl' := hlow (n + 1)
  omega
end BalanceSpecification
