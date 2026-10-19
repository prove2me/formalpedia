-- Prove2me | solution 1 for BookProof.KatoRellich.dense_range_add_bounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:33:55.249229+00:00
-- url     : https://prove2.me/submissions/b6e72229-5537-474b-95c7-5a139e8e9e1a

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore
import Theorems.Thm_BookProof_KatoRellich_dense_range_add_relBounded
-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.dense_range_add_bounded




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}


theorem solution (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (B : F →L[ℂ] F) (e : ℝ) (he : ‖B‖ < |e|)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) :
    Dense (Set.range fun x : D => (H x + B (x : F)) - ((e : ℂ) * Complex.I) • (x : F)) := by
  have hB0 : 0 ≤ ‖B‖ := norm_nonneg _
  have hepos : 0 < |e| := lt_of_le_of_lt hB0 he
  have he0 : e ≠ 0 := abs_pos.mp hepos
  have := BookProof.KatoRellich.dense_range_add_relBounded H (B.toLinearMap ∘ₗ D.subtype) hH
    (a := 0) (b := ‖B‖) le_rfl hB0 he0
    (fun x => by simpa using B.le_opNorm (x : F))
    (by rw [zero_add, div_lt_one hepos]; exact he) hdense
  simpa using this

