-- Prove2me | solution 1 for BhangaleHypergraph.Main.relational_completeness
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:33:07.188445+00:00
-- url     : https://prove2.me/submissions/665e50d9-1f0a-4853-b72e-b51c9881a74c

import Definitions.Def_BhangaleHypergraph_Main_Relational

open BhangaleHypergraph.Main

theorem solution (G : Layered) (C : ℕ) (hC : 2 ≤ C)
    (hlayers : G.layers = C + 1) (hsat : Satisfiable G) :
    RelColorable (Relational G C) 2 := by
  classical
  obtain ⟨σ, hσ⟩ := hsat
  let color : Occurrence G C → Fin 2 := fun a =>
    if σ a.1 ∈ a.2.val then 0 else 1
  have hgen : ∀ a b, Identification G C a b → color a = color b := by
    intro a b hab
    rcases hab with ⟨e, B, hB, hA, rfl, rfl⟩
    simp [color, Preimage, hσ e]
  refine ⟨Quot.lift color hgen, ?_⟩
  intro u v w htriple
  rcases htriple with ⟨x, A, B, D, hNAE, hu, hv, hw⟩
  have hu' : u = Quot.mk (Identification G C) ⟨x, A⟩ := by simpa using hu
  have hv' : v = Quot.mk (Identification G C) ⟨x, B⟩ := by simpa using hv
  have hw' : w = Quot.mk (Identification G C) ⟨x, D⟩ := by simpa using hw
  subst u
  subst v
  subst w
  change ¬ (color ⟨x, A⟩ = color ⟨x, B⟩ ∧ color ⟨x, B⟩ = color ⟨x, D⟩)
  intro heq
  by_cases hA : σ x ∈ A.val
  · by_cases hB : σ x ∈ B.val
    · have hD : σ x ∉ D.val := by
        intro hD
        have hmem : σ x ∈ A.val ∩ B.val ∩ D.val := by simp [hA, hB, hD]
        rw [hNAE.2] at hmem
        simpa using hmem
      simp [color, hA, hB, hD] at heq
    · simp [color, hA, hB] at heq
  · by_cases hB : σ x ∈ B.val
    · simp [color, hA, hB] at heq
    · have hD : σ x ∈ D.val := by
        have hmem : σ x ∈ A.val ∪ B.val ∪ D.val := by
          rw [hNAE.1]
          exact Finset.mem_univ _
        simpa [hA, hB] using hmem
      simp [color, hA, hB, hD] at heq
