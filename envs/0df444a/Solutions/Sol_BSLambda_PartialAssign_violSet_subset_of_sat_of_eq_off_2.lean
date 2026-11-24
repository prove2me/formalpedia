-- Prove2me | solution 2 for BSLambda.PartialAssign.violSet_subset_of_sat_of_eq_off
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:01:48.395714+00:00
-- url     : https://prove2.me/submissions/2778cf6d-66cc-4cd5-8c6b-7f8b58ffa128

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Theorems.Thm_BSLambda_PartialAssign_Sat_eq_of_fixed
public import Theorems.Thm_BSLambda_PartialAssign_mem_violSet_iff_exists_ne

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V]
namespace BSLambda.PartialAssign
theorem _root_.solution {P : PartialAssign V} {x y : Input V} {A : Finset V}
    (hx : P.Sat x) (h : ∀ v ∉ A, y v = x v) : P.violSet y ⊆ A := by
  intro v hv
  by_contra hvA
  obtain ⟨b, hb, hne⟩ := mem_violSet_iff_exists_ne.1 hv
  exact hne ((h v hvA).trans (hx.eq_of_fixed hb))
end BSLambda.PartialAssign
