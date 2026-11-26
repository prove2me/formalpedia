-- Prove2me | solution 1 for FixedOrderFactor.sum_char_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:10:13.645545+00:00
-- url     : https://prove2.me/submissions/a324aa05-c615-49cd-87f8-75631bb3e3e7

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_char_all__ce659e42cafe


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution (p : ℕ) [Fact p.Prime] {m n : ℕ} (hmn : m ≠ n) (hm : m < p) (hn : n < p)
    (hn0 : n ≠ 0) :
    ∑ χ : DirichletCharacter ℂ p, χ m * starRingEnd ℂ (χ n) = 0 :=
  sum_char_all' p hmn hm hn hn0
end FixedOrderFactor
