-- Prove2me | solution 1 for DeletionCode.BubbleCatalogue.wordSpectrum_eq_pathSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:42.905639+00:00
-- url     : https://prove2.me/submissions/7a2328c4-6252-49ef-9eb4-cda6f044e3f0

import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_ConnectedBlocks
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_DeletionCode_BubbleCatalogue
import Theorems.Thm_DeletionCode_SpectrumLocalization_wordSpectrum_eq_windowSum


set_option autoImplicit true
open DeletionCode DeletionCode.BubbleCatalogue
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport BubbleContextGeometry SpectrumLocalization
open scoped BigOperators
namespace DeletionCode.BubbleCatalogue
theorem _root_.solution (x : Letters) (n L : ℕ) (hn : L ≤ n) :
    wordSpectrum x n L = pathSpectrum x L (n - L) := by
  classical
  funext g
  rw [wordSpectrum_eq_windowSum x n L (by omega)]
  unfold windowSum pathSpectrum
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if gram x L i = g then (1 : ℤ) else 0) (n - L + 1)]
  have heq : n + 1 - L = n - L + 1 := by omega
  simp only [heq, Nat.zero_add]
end DeletionCode.BubbleCatalogue
