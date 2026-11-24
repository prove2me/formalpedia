-- Prove2me | solution 1 for BondySimonovits.anc_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:03:52.517204+00:00
-- url     : https://prove2.me/submissions/66b478be-a371-4ccc-a5ba-5e104dacd0d2

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} (K : SimpleGraph V)
variable {K} {par : V → V} {x : V}
  (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
    K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
include hpar
omit hpar
namespace BondySimonovits
theorem _root_.solution (v : V) : anc K par x (K.dist x v) v = v := by
  simp [anc]
end BondySimonovits
