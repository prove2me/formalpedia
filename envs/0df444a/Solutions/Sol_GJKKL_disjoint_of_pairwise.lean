-- Prove2me | solution 1 for GJKKL.disjoint_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:31.098746+00:00
-- url     : https://prove2.me/submissions/739032f9-e21e-4414-a7bb-cdd6c69a5b8e

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V]
namespace GJKKL
theorem _root_.solution : ∀ {h : List (Finset V)}, h.Pairwise Disjoint →
    ∀ {e f : Finset V}, e ∈ h → f ∈ h → e ≠ f → Disjoint e f
  | [], _, _, _, he, _, _ => absurd he List.not_mem_nil
  | a :: t, hp, e, f, he, hf, hef => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp he with rfl | he'
    · rcases List.mem_cons.mp hf with rfl | hf'
      · exact absurd rfl hef
      · exact hp.1 f hf'
    · rcases List.mem_cons.mp hf with rfl | hf'
      · exact (hp.1 e he').symm
      · exact solution hp.2 he' hf' hef
end GJKKL
