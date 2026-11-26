-- Prove2me | solution 1 for FixedOrderFactor.correctionFactor_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:08:30.065099+00:00
-- url     : https://prove2.me/submissions/ad8fcdff-982a-44f1-b9a2-161cc2a06991

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_correctionFactor_even__20a8b73c46be


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {k : ℕ} (hk : 0 < k) :
    correctionFactor ∅ (2 * k) =
      -((Nat.choose (4 * k) (2 * k) : ℝ) * (bernoulli (2 * k) : ℝ) ^ 2 /
        (2 * (bernoulli (4 * k) : ℝ))) :=
  correctionFactor_even' hk
end FixedOrderFactor
