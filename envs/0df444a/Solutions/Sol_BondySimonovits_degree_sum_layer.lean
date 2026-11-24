-- Prove2me | solution 1 for BondySimonovits.degree_sum_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:12:10.524464+00:00
-- url     : https://prove2.me/submissions/e2a0b119-7a8b-433d-af1b-4dd2e50efd02

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
public import Theorems.Thm_BondySimonovits_ecount_union_right
public import Theorems.Thm_BondySimonovits_layer_disjoint
public import Theorems.Thm_BondySimonovits_nbrs_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [Fintype V] [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
variable (f : V → Bool) (hf : ∀ u v, K.Adj u v → f u ≠ f v)
include hf
namespace BondySimonovits
theorem _root_.solution (x : V) (i : ℕ) :
    ∑ u ∈ layer K x i, (univ.filter (K.Adj u)).card =
      ecount K (layer K x i) (layer K x (i - 1)) + ecount K (layer K x i) (layer K x (i + 1)) := by
  rw [← ecount_union_right K _ _ _ (layer_disjoint K x (by omega))]
  unfold ecount
  exact Finset.sum_congr rfl (fun u hu => by rw [nbrs_eq K f hf x i u hu])
end BondySimonovits
