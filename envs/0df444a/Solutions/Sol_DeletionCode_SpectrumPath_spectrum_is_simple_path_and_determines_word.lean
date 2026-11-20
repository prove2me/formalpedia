-- Prove2me | solution 1 for DeletionCode.SpectrumPath.spectrum_is_simple_path_and_determines_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:38.225103+00:00
-- url     : https://prove2.me/submissions/afcfb195-5898-4a1e-bab7-54da0bc6bed6

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_WordPaths
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_SpectrumPath
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_boolean
import Theorems.Thm_DeletionCode_SpectrumPath_vertex_path_injective
import Theorems.Thm_DeletionCode_SpectrumPath_spectrum_support_path
import Theorems.Thm_DeletionCode_SpectrumPath_path_edge_endpoints
import Theorems.Thm_DeletionCode_SpectrumPath_equal_spectrum_recovers_word

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPath
open Windows SignedSupport
open scoped BigOperators
namespace DeletionCode.SpectrumPath
theorem _root_.solution (word : Letters) (n L : ℕ)
    (hL : 1 ≤ L) (hn : L ≤ n) (hunique : KUnique word n (L - 1)) :
    (∀ g, wordSpectrum word n L g = 0 ∨ wordSpectrum word n L g = 1) ∧
    Function.Injective (fun i : Fin (n - L + 2) => vertexAt word L i.val) ∧
    (∀ g, wordSpectrum word n L g ≠ 0 ↔ ∃ i : Fin (n - L + 1), gram word L i.val = g) ∧
    (∀ i : Fin (n - L + 1),
      gramPrefix (gram word L i.val) = vertexAt word L i.val ∧
      gramSuffix (gram word L i.val) = vertexAt word L (i.val + 1)) ∧
    (∀ z : Letters, wordSpectrum z n L = wordSpectrum word n L → Agree z 0 word 0 n) := by
  exact ⟨spectrum_boolean word n L hunique,
    vertex_path_injective word n L hL hn hunique,
    spectrum_support_path word n L hn,
    fun i => path_edge_endpoints word L i.val,
    fun z h => equal_spectrum_recovers_word word z n L hL hn hunique h⟩
end DeletionCode.SpectrumPath
