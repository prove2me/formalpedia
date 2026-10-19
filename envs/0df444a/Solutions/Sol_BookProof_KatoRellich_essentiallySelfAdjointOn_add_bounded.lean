-- Prove2me | solution 1 for BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T14:15:43.55285+00:00
-- url     : https://prove2.me/submissions/77745a9f-029f-4850-9ad7-10e61ced9d4c

-- Generated from ChapterKatoRellichDeficiency.lean — solution of BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Theorems.Thm_BookProof_KatoRellich_deficiencyTrivialAt_of_dense
import Theorems.Thm_BookProof_KatoRellich_dense_range_add_bounded
import Theorems.Thm_BookProof_FarisLavine_deficiencyTrivialAt_of_dense_range
import Theorems.Thm_BookProof_FarisLavine_dense_range_of_deficiencyTrivialAt
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.KatoRellich




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by

  set K : D →ₗ[ℂ] F := H + (B.toLinearMap ∘ₗ D.subtype) with hK
  have hKapply : ∀ x : D, K x = H x + B (x : F) := fun x => rfl
  have hKsymm : SymmetricOn D K := by
    intro x y
    simp only [hKapply, inner_add_left, inner_add_right, hH x y, hB (x : F) (y : F)]
  -- `H` has trivial deficiency spaces at every non-real point
  have hHall : ∀ σ : ℂ, σ.im ≠ 0 → DeficiencyTrivialAt D H σ := by
    intro σ hσ
    refine deficiencyTrivialAt_of_dense_range H hH 1 one_ne_zero σ hσ ?_ ?_
    · have := dense_range_of_deficiencyTrivialAt H ((1 : ℝ) * Complex.I) (by simpa using hesa.2)
      simpa using this
    · simpa using hesa.1
  -- pick `e` with `|e| > ‖B‖`
  set e : ℝ := ‖B‖ + 1 with hedef
  have he : ‖B‖ < |e| := by
    rw [hedef, abs_of_nonneg (by positivity)]
    linarith
  have he0 : e ≠ 0 := by
    have : (0 : ℝ) < e := by rw [hedef]; positivity
    exact ne_of_gt this
  -- density of the ranges of `K ∓ e i`
  have hdenseH : ∀ d : ℝ, d ≠ 0 →
      Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    refine dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (hHall _ ?_)
    simp [hd]
  have hdenseK : ∀ d : ℝ, ‖B‖ < |d| →
      Dense (Set.range fun x : D => (H x + B (x : F)) - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [h] at hd
      simp at hd
      linarith [norm_nonneg B]
    exact dense_range_add_bounded H hH B d hd (hdenseH d hd0)
  have habs : ‖B‖ < |(-e)| := by rwa [abs_neg]
  have hdefK : DeficiencyTrivialAt D K ((e : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_dense K _ ?_
    have hconj : (starRingEnd ℂ) ((e : ℂ) * Complex.I) = ((-e : ℝ) : ℂ) * Complex.I := by
      push_cast
      simp [mul_comm]
    rw [hconj]
    simpa [hKapply] using hdenseK (-e) habs
  have hdenseKe : Dense (Set.range fun x : D => K x - ((e : ℂ) * Complex.I) • (x : F)) := by
    simpa [hKapply] using hdenseK e he
  exact ⟨deficiencyTrivialAt_of_dense_range K hKsymm e he0 Complex.I (by simp) hdenseKe hdefK,
    deficiencyTrivialAt_of_dense_range K hKsymm e he0 (-Complex.I) (by simp) hdenseKe hdefK⟩
