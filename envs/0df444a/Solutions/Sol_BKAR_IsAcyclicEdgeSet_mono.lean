-- Prove2me | solution 1 for BKAR.IsAcyclicEdgeSet.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:30.513294+00:00
-- url     : https://prove2.me/submissions/1f4c5271-e737-4fbf-b10e-05f8f7006c84

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsPath_mono_of_forall_mem
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono_of_forall_mem

set_option autoImplicit false
open BKAR
open BKAR.IsAcyclicEdgeSet
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.IsAcyclicEdgeSet
theorem _root_.solution {S T : Finset (Edge V)}
    (hS : IsAcyclicEdgeSet S) (hsub : T ⊆ S) :
    IsAcyclicEdgeSet T := by
  classical
  rcases hS with ⟨data⟩
  refine ⟨{
    inSameComponent := fun i j =>
      ∃ γ : List (Edge V), data.isSimplePath γ i j ∧
        ∀ e ∈ γ, e ∈ T
    isSimplePath := fun γ i j =>
      data.isSimplePath γ i j ∧ ∀ e ∈ γ, e ∈ T
    pathIn := fun _ _ h => Classical.choose h
    pathIn_isSimple := ?_
    isSimplePath_iff := ?_
    sameComponent_of_simplePath := ?_
    path_unique := ?_
    path_edges_mem := ?_
    edge_isSimplePath := ?_ }⟩
  · intro i j h
    exact Classical.choose_spec h
  · intro i j γ
    constructor
    · intro hγ
      exact
        (data.isSimplePath_iff.mp hγ.1).mono_of_forall_mem hγ.2
    · intro hγ
      constructor
      · exact data.isSimplePath_iff.mpr (hγ.mono hsub)
      · exact hγ.edge_mem
  · intro i j γ hγ
    exact ⟨γ, hγ⟩
  · intro i j γ₁ γ₂ hγ₁ hγ₂
    exact data.path_unique hγ₁.1 hγ₂.1
  · intro i j γ hγ e he
    exact hγ.2 e he
  · intro e he
    constructor
    · exact data.edge_isSimplePath (hsub he)
    · intro x hx
      rw [List.mem_singleton] at hx
      exact hx ▸ he
end BKAR.IsAcyclicEdgeSet
