-- Prove2me | solution 1 for BondySimonovits.anc_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:35.384963+00:00
-- url     : https://prove2.me/submissions/9815161c-787f-481a-adc4-40fe62c29f1a

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Theorems.Thm_BondySimonovits_anc_spec

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
namespace BondySimonovits
theorem _root_.solution {v : V} (hr : K.Reachable x v) : anc K par x 0 v = x := by
  have h := anc_spec hpar hr (Nat.zero_le _)
  exact ((h.1.symm.dist_eq_zero_iff).1 (by rw [SimpleGraph.dist_comm]; exact h.2))
end BondySimonovits
