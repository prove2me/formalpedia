-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.ratio_cj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:40.68044+00:00
-- url     : https://prove2.me/submissions/b223a490-5c13-4f2e-b485-5f3191b6744c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_ratio_eq_of_comm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_ratio_map_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags
theorem _root_.solution (A S : Subgroup G) (g : G)
    (hA1 : A.relIndex S ≠ 0) (hA2 : S.relIndex A ≠ 0)
    (hB1 : (cj g A).relIndex S ≠ 0) (hB2 : S.relIndex (cj g A) ≠ 0)
    (hU : S.relIndex (cj g S) ≠ 0 → (cj g S).relIndex S ≠ 0 →
      S.relIndex (cj g S) = (cj g S).relIndex S) :
    ratio (cj g A) S = ratio A S := by
  have m1 : (cj g S).relIndex (cj g A) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA2
  have m2 : (cj g A).relIndex (cj g S) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA1
  have hTS : (cj g S).relIndex S ≠ 0 := Subgroup.relIndex_ne_zero_trans m1 hB1
  have hST : S.relIndex (cj g S) ≠ 0 := Subgroup.relIndex_ne_zero_trans hB2 m2
  have hk := (hU hST hTS).symm
  rw [ratio_eq_of_comm S (cj g S) (cj g A) hk hTS]
  exact ratio_map_equiv (MulAut.conj g) A S
end Formalism.L2.SG.Pf.RelativeIndexFlags
