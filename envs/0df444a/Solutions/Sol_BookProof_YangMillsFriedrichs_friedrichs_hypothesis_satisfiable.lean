-- Prove2me | solution 1 for BookProof.YangMillsFriedrichs.friedrichs_hypothesis_satisfiable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:14.510279+00:00
-- url     : https://prove2.me/submissions/4606fb64-123c-4da7-82e5-463b39acfa12

-- Generated from ChapterYangMillsFriedrichs.lean — solution of BookProof.YangMillsFriedrichs.friedrichs_hypothesis_satisfiable
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
open BookProof.YangMillsFriedrichs



















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}





















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F)
    (hsym : SymmetricOn (⊤ : Submodule ℂ F) H)
    (hpos : ∀ x : (⊤ : Submodule ℂ F), 0 ≤ quadForm H x) :
    IsPositiveSelfAdjointExtension H H := by

  refine ⟨fun x => ⟨trivial, by congr⟩, hsym, hpos, fun w u hw => ⟨trivial, ?_⟩⟩
  have hzero : ∀ v : (⊤ : Submodule ℂ F), (inner ℂ (v : F) (H ⟨w, trivial⟩ - u) : ℂ) = 0 := by
    intro v
    rw [inner_sub_right, ← hw v, ← hsym v ⟨w, trivial⟩]
    ring
  have hd : (inner ℂ (H ⟨w, trivial⟩ - u) (H ⟨w, trivial⟩ - u) : ℂ) = 0 :=
    hzero ⟨H ⟨w, trivial⟩ - u, trivial⟩
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hd)
