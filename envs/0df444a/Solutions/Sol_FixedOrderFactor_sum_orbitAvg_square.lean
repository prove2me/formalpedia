-- Prove2me | solution 1 for FixedOrderFactor.sum_orbitAvg_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:11:19.819851+00:00
-- url     : https://prove2.me/submissions/52ca8512-f8cf-43c8-b997-9d9fdb5eb755

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
public import Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c


set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {M : ℕ} [NeZero M] {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : ZMod M => IsUnit y ∧ y ^ 2 = a),
      ∑ t ∈ Finset.range s, orbitAvg s (((ZMod.castHom hs (ZMod s) y).val + 1) * t) =
      s * sqrtCount M a s :=
  sum_orbitAvg_square' hs a
end FixedOrderFactor
