-- Prove2me | solution 1 for BayesianPersuasion.Proof.convexHull_fixed_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:08.742794+00:00
-- url     : https://prove2.me/submissions/b93228b4-9f7d-4753-85d6-5653aebb45f5

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic
public import Definitions.Def_BayesianPersuasion_CompactHull
public import Theorems.Thm_BayesianPersuasion_Proof_convexHull_finite_support
public import Theorems.Thm_BayesianPersuasion_Proof_sum_pad

set_option autoImplicit true
@[expose] public section
public section
open Set Finset
open BayesianPersuasion BayesianPersuasion.Proof
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
namespace BayesianPersuasion.Proof
theorem _root_.solution {s : Set E} (hs : s.Nonempty) {x : E}
    (hx : x ∈ convexHull ℝ s) :
    ∃ (w : Belief (Fin (Module.finrank ℝ E + 1)))
      (z : Fin (Module.finrank ℝ E + 1) → s), ∑ j, w.val j • (z j).val = x := by
  classical
  obtain ⟨z₀, hz₀⟩ := hs
  obtain ⟨k, hk, z, w, hz, hbar⟩ := convexHull_finite_support hx
  let wp : Fin (Module.finrank ℝ E + 1) → ℝ :=
    fun j => if h : j.val < k then w.val ⟨j.val, h⟩ else 0
  let zp : Fin (Module.finrank ℝ E + 1) → s :=
    fun j => if h : j.val < k then ⟨z ⟨j.val, h⟩, hz _⟩ else ⟨z₀, hz₀⟩
  have hw : (∀ j, 0 ≤ wp j) ∧ ∑ j, wp j = 1 := by
    constructor
    · intro j; dsimp [wp]; split_ifs <;> simp_all [w.property.1]
    · exact (sum_pad hk w.val).trans w.property.2
  refine ⟨⟨wp, hw⟩, zp, ?_⟩
  have hterm : ∀ j, wp j • (zp j).val =
      if h : j.val < k then w.val ⟨j.val, h⟩ • z ⟨j.val, h⟩ else 0 := by
    intro j; dsimp [wp, zp]; split_ifs <;> simp
  simp_rw [hterm]
  exact (sum_pad hk (fun j => w.val j • z j)).trans hbar
end BayesianPersuasion.Proof
