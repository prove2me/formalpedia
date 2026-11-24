-- Prove2me | solution 1 for BondySimonovits.anc_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:21.875011+00:00
-- url     : https://prove2.me/submissions/a7ac6466-d894-4a04-b8f1-62dd48fc25c7

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
theorem _root_.solution {t : ℕ} {v : V} (hr : K.Reachable x v) (ht : t < K.dist x v) :
    K.Adj (anc K par x (t + 1) v) (anc K par x t v) := by
  have hs := anc_spec hpar hr (show t + 1 ≤ K.dist x v by omega)
  have key : anc K par x t v = par (anc K par x (t + 1) v) := by
    unfold anc
    rw [← Function.iterate_succ_apply' par]
    congr 1
    omega
  rw [key]
  exact (hpar _ hs.1 (by omega)).1
end BondySimonovits
