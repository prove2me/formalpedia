-- Prove2me | solution 1 for FixedOrderFactor.sum_orbitAvg_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:10:44.458057+00:00
-- url     : https://prove2.me/submissions/f8ac9f28-8a54-413e-82de-41fba4a25cbb

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_mul__4157f1f1226d


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ Finset.range s, orbitAvg s (c * t) = if s ∣ c then (s : ℂ) else 0 :=
  sum_orbitAvg_mul' hs c
end FixedOrderFactor
