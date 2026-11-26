-- Prove2me | solution 1 for BKAR.orderedSimplexIntegralAux_congr_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:37:06.901859+00:00
-- url     : https://prove2.me/submissions/24dec91d-d15d-47bf-8b68-a867c7372827

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same


attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.orderedSimplexParams_cons

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top : ℝ) :
    ∀ (order : List (Edge V)) {f g : List ℝ → ℝ},
      (∀ ts, ts.length = order.length → f ts = g ts) →
        orderedSimplexIntegralAux top order f =
          orderedSimplexIntegralAux top order g
  | [], _, _, hfg => hfg [] rfl
  | _ :: order, f, g, hfg => by
      apply intervalIntegral.integral_congr
      intro t _
      exact solution t order
        (f := fun ts => f (t :: ts))
        (g := fun ts => g (t :: ts))
        (fun ts hlen => hfg (t :: ts) (by simp [hlen]))
end BKAR
