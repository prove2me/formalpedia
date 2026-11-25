-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.unitLat_isLatIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:26:45.716509+00:00
-- url     : https://prove2.me/submissions/7d683c98-c483-4cd3-8bce-ac099a571068

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : IsLatIn (⊤ : Submodule K K) (unitLat K) := by
  unfold IsLatIn unitLat
  refine ⟨Submodule.fg_span_singleton _, ?_⟩
  first
    | (rw [Submodule.span_span_of_tower]
       exact eq_top_iff.2 fun x _ => Submodule.mem_span_singleton.2 ⟨x, by simp⟩)
    | (refine eq_top_iff.2 fun x _ => ?_
       have h1 : (1 : K) ∈ (Submodule.span (𝓞 K) {(1 : K)} : Set K) := Submodule.subset_span rfl
       have h2 := Submodule.smul_mem (Submodule.span K (Submodule.span (𝓞 K) {(1 : K)} : Set K)) x
         (Submodule.subset_span h1)
       simpa using h2)
end Formalism.EigenvalueLevelCeiling
