-- Prove2me | solution 1 for DeletionCode.SpectrumPrefixChange.common_suffix_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:43.426177+00:00
-- url     : https://prove2.me/submissions/c24b5aaf-7fe2-44a5-9f23-8056c68f287f

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
import Theorems.Thm_DeletionCode_SpectrumPrefixChange_prefix_change
import Theorems.Thm_DeletionCode_SpectrumPrefixChange_common_prefix

set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization
namespace DeletionCode.SpectrumPrefixChange
theorem _root_.solution (a b common p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hcommon : L - 1 ≤ common.length) (g : Gram L) :
    spectrum ((b ++ common) ++ q) L g - spectrum ((b ++ common) ++ p) L g =
      spectrum ((a ++ common) ++ q) L g - spectrum ((a ++ common) ++ p) L g := by
  have hp : L ≤ (common ++ p).length + 1 := by
    simp only [List.length_append]
    omega
  have hq : L ≤ (common ++ q).length + 1 := by
    simp only [List.length_append]
    omega
  simp only [List.append_assoc]
  rw [prefix_change b _ _ L hL hp hq (common_prefix common p q L hcommon),
    prefix_change a _ _ L hL hp hq (common_prefix common p q L hcommon)]
end DeletionCode.SpectrumPrefixChange
