-- Prove2me | solution 1 for BondySimonovits.anc_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:06:00.018833+00:00
-- url     : https://prove2.me/submissions/de87b3b3-dc5b-40ec-83d0-6e49e77ae2db

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
public import Definitions.Def_BondySimonovitsLib_BSLayers
public import Theorems.Thm_BondySimonovits_iterate_par_spec

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
theorem _root_.solution {t : ℕ} {v : V} (hr : K.Reachable x v) (ht : t ≤ K.dist x v) :
    K.Reachable x (anc K par x t v) ∧ K.dist x (anc K par x t v) = t := by
  obtain ⟨h1, h2⟩ := iterate_par_spec hpar (K.dist x v - t) v hr (by omega)
  exact ⟨h1, by unfold anc; omega⟩
end BondySimonovits
