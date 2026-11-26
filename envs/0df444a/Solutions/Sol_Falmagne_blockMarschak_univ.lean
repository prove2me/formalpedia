-- Prove2me | solution 1 for Falmagne.blockMarschak_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:19.010801+00:00
-- url     : https://prove2.me/submissions/fe4163aa-ba88-4eb4-842b-35550dd7c34a

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
public import Theorems.Thm_Falmagne_mem_lowerContour
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.mem_lowerContour
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
namespace Falmagne
theorem _root_.solution (p : Finset X → X → ℝ) (x : X) :
    blockMarschak p x univ = p univ x := by
  have hfilter : univ.filter (fun B : Finset X => univ ⊆ B) = {univ} := by
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => Subset.antisymm (subset_univ B) h, fun h => by simp [h]⟩
  unfold blockMarschak upperMobius
  rw [hfilter]
  simp
end Falmagne
