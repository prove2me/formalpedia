-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_boolean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:34.515774+00:00
-- url     : https://prove2.me/submissions/7088fd42-17e6-4d83-b955-ce3cb8937716

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_at_occurrence_one
import Theorems.Thm_DeletionCode_SignedSupport_wordSpectrum_nonzero_occurs


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L : ℕ)
    (hunique : KUnique word n (L - 1)) :
    ∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1 := by
  classical
  intro g
  by_cases hzero : wordSpectrum word n L g = 0
  · exact Or.inl hzero
  · obtain ⟨a, ha, hg⟩ := wordSpectrum_nonzero_occurs word n L g hzero
    exact Or.inr (spectrum_at_occurrence_one word n L a g hunique ha hg)
end DeletionCode.SpectrumPath
