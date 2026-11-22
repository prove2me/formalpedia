-- Prove2me | solution 1 for Formalism.CountingSumsFrames.sum_Icc_dimHar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:42.40173+00:00
-- url     : https://prove2.me/submissions/f8c1e206-5c29-47ae-8a60-09e680a89fc7

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicLevelCountRec
import Theorems.Thm_Formalism_CountingSumsFrames_harmonic_level_count_rec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ∑ j ∈ Icc J (min A B), dimHar k' (A - j) (B - j) = dimPol k' (A - J) * dimPol k' (B - J) := by
  have e : Icc J (min A B) = Ico J (J + (min (A - J) (B - J) + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
  rw [e, Finset.sum_Ico_eq_sum_range,
    show J + (min (A - J) (B - J) + 1) - J = min (A - J) (B - J) + 1 by omega,
    ← harmonic_level_count_rec k' (A - J) (B - J)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show A - (J + i) = A - J - i by omega, show B - (J + i) = B - J - i by omega]
end Formalism.CountingSumsFrames
