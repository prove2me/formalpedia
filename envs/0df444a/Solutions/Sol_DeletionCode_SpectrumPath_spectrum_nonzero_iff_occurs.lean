-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_nonzero_iff_occurs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:40.634538+00:00
-- url     : https://prove2.me/submissions/af48f32a-5397-41ea-97c9-170d3e1c9309

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_at_occurrence_positive
import Theorems.Thm_DeletionCode_SignedSupport_wordSpectrum_nonzero_occurs


set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L : ℕ) (g : Gram L) :
    wordSpectrum word n L g ≠ 0 ↔ ∃ a, a + L ≤ n ∧ gram word L a = g := by
  constructor
  · exact wordSpectrum_nonzero_occurs word n L g
  · rintro ⟨a, ha, hg⟩
    exact ne_of_gt (spectrum_at_occurrence_positive word n L a g ha hg)
end DeletionCode.SpectrumPath
