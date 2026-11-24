-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Cas_comm_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:07.361532+00:00
-- url     : https://prove2.me/submissions/6c09bfc3-7937-4df1-8a71-f9d5712d5b62

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_apply
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_Cas
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_midAct_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p LL j0).Cas (glAct p LL J c d F) = glAct p LL J c d ((GA p LL j0).Cas F) := by
  rw [glAct_split LL hJ c d, LinearMap.add_apply, LinearMap.add_apply, map_add]
  congr 1
  · exact ((GA p LL j0).E_Cas c d F).symm
  · rw [GlW.Cas_apply, GlW.Cas_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    show glAct p LL j0 a b (glAct p LL j0 b a (midAct p LL j0 J c d F)) =
      midAct p LL j0 J c d (glAct p LL j0 a b (glAct p LL j0 b a F))
    rw [← midAct_comm, ← midAct_comm]
end Formalism.GM.DimensionMonotonicity
