-- Prove2me | solution 1 for BookProof.ChapterA3w.weyl_invariant_complement
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:30:16.107147+00:00
-- url     : https://prove2.me/submissions/80d5df7e-0b30-4826-8b8e-b417dcc608cf

-- Generated from ChapterA3w.lean — theorem BookProof.ChapterA3w.weyl_invariant_complement
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3w
open BookProof.ChapterA3w


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3q

theorem solution (h : WeylCompleteReducibility)
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (W : Submodule ℂ V)
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W' : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W' := by
  exact h ρ W hW

#print axioms solution

