-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_lw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:30.52559+00:00
-- url     : https://prove2.me/submissions/2ab5404d-7e12-40f3-9d92-de2b497210a7

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

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
theorem _root_.solution {M : Type} [AddCommGroup M] (LL : Letters N) (j : ℕ) (a b : Fin r) (w : Fin N × Fin r → M)
    (hw : ∀ i c c', w (i, c) = w (i, c')) {D : M} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] w D) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] w D := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight w d = D := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1 h2
  · have h3 := wh_XD (K := ℚ_[p]) w (i, b) (i, a) d (coeff d x)
    have e : D = Finsupp.weight w d - w (i, b) + w (i, a) := by
      rw [hwd, hw i b a, sub_add_cancel]
    rw [e]
    exact h3
  · have h3 := wh_XD (K := ℚ_[p]) w (i, a) (i, b) d (coeff d x)
    have e : D = Finsupp.weight w d - w (i, a) + w (i, b) := by
      rw [hwd, hw i a b, sub_add_cancel]
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Formalism.GM.DimensionMonotonicity
