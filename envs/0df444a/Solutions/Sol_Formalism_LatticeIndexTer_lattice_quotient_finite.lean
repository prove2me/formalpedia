-- Prove2me | solution 1 for Formalism.LatticeIndexTer.lattice_quotient_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:09.517598+00:00
-- url     : https://prove2.me/submissions/ccf2582e-2319-484f-9194-cb65b62b65ea

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_GeneralBFactSecondFurther_Imports
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxBase
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_exists_smul_le
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexLength_len_ne_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
open scoped Pointwise
open LatticeIndexLength
namespace Formalism.LatticeIndexTer
theorem _root_.solution : LatFinite := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B hA hB
  obtain ⟨d, hd, h⟩ := exists_smul_le (K := K) A B hA.1 hB.2
  exact len_ne_top A B hA.1 d hd h
end Formalism.LatticeIndexTer
