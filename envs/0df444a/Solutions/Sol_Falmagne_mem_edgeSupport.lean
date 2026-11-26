-- Prove2me | solution 1 for Falmagne.mem_edgeSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:24:39.471847+00:00
-- url     : https://prove2.me/submissions/a1308e58-5fd3-4c75-910e-9bb145f141d3

module
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Flow
public import Theorems.Thm_Falmagne_pathFlow_cons
public import Theorems.Thm_Falmagne_pathFlow_nil
attribute [local simp] Falmagne.pathFlow_cons
attribute [local simp] Falmagne.pathFlow_nil



set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {q : X → Finset X → ℝ} {m : ℝ} {x : X} {A : Finset X}
namespace Falmagne
theorem _root_.solution (q : X → Finset X → ℝ) (e : X × Finset X) :
    e ∈ edgeSupport q ↔ e.1 ∈ e.2 ∧ 0 < q e.1 e.2 := by
  simp [edgeSupport]
end Falmagne
