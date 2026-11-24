-- Prove2me | solution 1 for BondySimonovits.anc_anc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:09:21.436509+00:00
-- url     : https://prove2.me/submissions/0aaeebbe-7f2d-4e51-ada6-f416e49926d9

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
theorem _root_.solution {r t : ℕ} {v : V} (hr : K.Reachable x v) (hrt : r ≤ t) (ht : t ≤ K.dist x v) :
    anc K par x r (anc K par x t v) = anc K par x r v := by
  have h := (anc_spec hpar hr ht).2
  unfold anc at h ⊢
  rw [h, ← Function.iterate_add_apply]
  congr 1
  omega
end BondySimonovits
