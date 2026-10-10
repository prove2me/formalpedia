-- Prove2me | solution 1 for BookProof.ClosureUniqueness.eq_of_opGraph_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:16:22.423095+00:00
-- url     : https://prove2.me/submissions/1c6a1e7c-8f70-41fd-b472-91801a0760e4

-- Generated from ChapterClosureUniqueness.lean — solution of BookProof.ClosureUniqueness.eq_of_opGraph_eq
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ClosureUniqueness




open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom₁ →ₗ[ℂ] F} {B : Dom₂ →ₗ[ℂ] F} (h : opGraph A = opGraph B) :
    Dom₁ = Dom₂ ∧ ∀ (x : F) (h₁ : x ∈ Dom₁) (h₂ : x ∈ Dom₂), A ⟨x, h₁⟩ = B ⟨x, h₂⟩ := by

  have key : ∀ (x : F) (h₁ : x ∈ Dom₁), ∃ h₂ : x ∈ Dom₂, B ⟨x, h₂⟩ = A ⟨x, h₁⟩ := by
    intro x h₁
    have hx : ((x : F), A ⟨x, h₁⟩) ∈ opGraph B := by
      rw [← h]; exact mem_opGraph A ⟨x, h₁⟩
    obtain ⟨w, hw⟩ := hx
    have hw1 : (w : F) = x := congrArg Prod.fst hw
    have hw2 : B w = A ⟨x, h₁⟩ := congrArg Prod.snd hw
    refine ⟨hw1 ▸ w.2, ?_⟩
    rw [← hw2]
    congr 1
    exact Subtype.ext hw1.symm
  have key' : ∀ (x : F) (h₂ : x ∈ Dom₂), ∃ h₁ : x ∈ Dom₁, A ⟨x, h₁⟩ = B ⟨x, h₂⟩ := by
    intro x h₂
    have hx : ((x : F), B ⟨x, h₂⟩) ∈ opGraph A := by
      rw [h]; exact mem_opGraph B ⟨x, h₂⟩
    obtain ⟨w, hw⟩ := hx
    have hw1 : (w : F) = x := congrArg Prod.fst hw
    have hw2 : A w = B ⟨x, h₂⟩ := congrArg Prod.snd hw
    refine ⟨hw1 ▸ w.2, ?_⟩
    rw [← hw2]
    congr 1
    exact Subtype.ext hw1.symm
  refine ⟨?_, fun x h₁ h₂ => ?_⟩
  · ext x
    exact ⟨fun hx => (key x hx).1, fun hx => (key' x hx).1⟩
  · obtain ⟨h₂', hval⟩ := key x h₁
    rw [← hval]
