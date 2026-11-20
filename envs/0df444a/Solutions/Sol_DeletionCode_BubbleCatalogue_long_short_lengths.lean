-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.long_short_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:36.27886+00:00
-- url     : https://prove2.me/submissions/318b2e2a-924c-4f36-b696-49911f2ce4b3

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_longWord_length
import Theorems.Thm_DeletionCode_CatalogueWords_BubbleWord_shortWord_length


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution {k : ℕ} (bubble : BubbleWord k) :
    bubble.longWord.length = windowLength k + (windowLength k - bubble.rho) ∧
      bubble.shortWord.length = windowLength k + (windowLength k - bubble.rho - 1) ∧
      1 ≤ windowLength k - bubble.rho := by
  have hlo := bubble.rho_lower
  have hhi := bubble.rho_upper
  simp only [bubble.longWord_length, bubble.shortWord_length, longLength, shortLength,
    BubbleWord.header, windowLength]
  omega
end DeletionCode.BubbleCatalogue
