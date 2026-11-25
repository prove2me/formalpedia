-- Prove2me | solution 1 for BayesianPersuasion.Proof.convexHull_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:04:01.622024+00:00
-- url     : https://prove2.me/submissions/4043fb8e-23d3-4e9b-b227-dce219d2050e

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull

set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
namespace BayesianPersuasion.Proof
theorem _root_.solution {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ (k : ℕ) (_ : k ≤ Module.finrank ℝ E + 1) (z : Fin k → E) (w : Belief (Fin k)),
      (∀ j, z j ∈ s) ∧ ∑ j, w.val j • z j = x := by
  obtain ⟨ι, hι, z, w, hz, hi, hw, hsum, hbar⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hcard, z ∘ e,
    ⟨w ∘ e, fun j => (hw (e j)).le, ?_⟩, fun j => hz ⟨e j, rfl⟩, ?_⟩
  · exact (e.sum_comp w).trans hsum
  · exact (e.sum_comp (fun j => w j • z j)).trans hbar
end BayesianPersuasion.Proof
