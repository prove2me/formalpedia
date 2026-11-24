-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.export_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:28:14.078417+00:00
-- url     : https://prove2.me/submissions/b1665026-26c0-4515-9ddc-adb7f5337d7d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexScale
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWExportTransfer
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_additive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_scaling


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : ExportTransfer := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M B N N' c e ε hM hB hN hN' hc he hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  rw [index_scaling O K V B N' ϖ u n hB hN' hϖ, index_scaling O K V B N ϖ u n hB hN hϖ]
    at hle
  have a := (index_additive O K V M N N' hM hN hN').2
  have b := (index_additive O K V B N N' hB hN hN').2
  have d : sIdx M N' - sIdx M N = sIdx B N' - sIdx B N := by omega
  have d' : (sIdx M N' : ℝ) - sIdx M N = sIdx B N' - sIdx B N := by exact_mod_cast d
  push_cast at hle
  rw [add_div, add_div] at hle
  have h1 : (sIdx M N' : ℝ) / e - sIdx M N / e = sIdx B N' / e - sIdx B N / e := by
    rw [← sub_div, ← sub_div, d']
  linarith
end Formalism.IrreducibleCountingLemmas.TW
