-- Prove2me | solution 1 for BookProof.KatoRellich.deficiencyTrivialAt_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:34:10.18937+00:00
-- url     : https://prove2.me/submissions/536c8e3c-6935-4e4d-8b02-bb39f76c0646

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore
-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.deficiencyTrivialAt_of_dense




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}


theorem solution (T : D →ₗ[ℂ] F) (z : ℂ)
    (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  have horth : ∀ u ∈ Set.range (fun x : D => T x - ((starRingEnd ℂ) z) • (x : F)),
      (inner ℂ u w : ℂ) = 0 := by
    rintro _ ⟨v, rfl⟩
    rw [inner_sub_left, inner_smul_left, hw v]; simp
  have hcl : IsClosed {u : F | (inner ℂ u w : ℂ) = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hall : ∀ u : F, (inner ℂ u w : ℂ) = 0 := by
    intro u
    have : closure (Set.range (fun x : D => T x - ((starRingEnd ℂ) z) • (x : F)))
        ⊆ {u : F | (inner ℂ u w : ℂ) = 0} := closure_minimal horth hcl
    exact this (hd.closure_eq ▸ Set.mem_univ u)
  exact inner_self_eq_zero.mp (hall w)

