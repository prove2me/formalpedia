-- Prove2me | solution 1 for DeletionCode.SpectrumPath.catalogue_window_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:19:48.384177+00:00
-- url     : https://prove2.me/submissions/897b3927-9a24-40ee-b9db-cac69dc873d8

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_is_simple_path_and_determines_word
import Theorems.Thm_DeletionCode_SpectrumPath_kunique_mono

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n k : ℕ)
    (hunique : KUnique word n k) (hn : HeaderRecovery.windowLength k ≤ n) :
    let L := HeaderRecovery.windowLength k
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by
  have hlarge : k ≤ HeaderRecovery.windowLength k - 1 := by
    dsimp [HeaderRecovery.windowLength]
    omega
  exact spectrum_is_simple_path_and_determines_word word n (HeaderRecovery.windowLength k)
    (by dsimp [HeaderRecovery.windowLength]; omega) hn
    (kunique_mono word n k (HeaderRecovery.windowLength k - 1) hunique hlarge)
end DeletionCode.SpectrumPath
