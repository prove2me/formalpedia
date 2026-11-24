-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.pol_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:08.106495+00:00
-- url     : https://prove2.me/submissions/753af96d-e2c1-45c0-a6be-f6b1ee4a1162

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_wL
import Theorems.Thm_Formalism_GM_M_FB_weight_wL


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
theorem _root_.solution (LL : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Pol p r LL ↔ IsWeightedHomogeneous (wL N r) x (fun i => (LL.deg i : ℤ)) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h d hd
    have hm : MultiDeg LL d := h (mem_support_iff.mpr hd)
    funext i
    rw [weight_wL]
    exact_mod_cast hm i
  · intro h d hd
    have hw := h (mem_support_iff.mp hd)
    show ∀ i, ∑ c, d (i, c) = LL.deg i
    intro i
    have h5 := congrFun hw i
    rw [weight_wL] at h5
    exact_mod_cast h5
end Formalism.GM.DimensionMonotonicity
