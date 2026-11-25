-- Prove2me | solution 1 for Formalism.DivisionValues.lattice_gluing_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:35.8857+00:00
-- url     : https://prove2.me/submissions/ff6782ec-8638-4ad7-bbac-9a94fb450174

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glueLat_spec
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open GluingInclusion Formalism.HermitianLatticesTheory
namespace Formalism.DivisionValues
theorem _root_.solution : LatticeGlueIndep := by
  classical
  intro K _ _ D L0 L1 h0 h1 S hS
  obtain ⟨hlat, hloc⟩ := glueLat_spec L0 (fun w => if w ∈ S then L1 else L0) h0
    (fun w => by by_cases hw : w ∈ S <;> simp only [hw, if_true, if_false] <;> assumption)
    (hS.subset (fun w hw => by
      by_contra hwS
      apply hw
      simp only [hwS, if_false]))
  refine ⟨_, ⟨hlat, fun w hw => ?_, fun w hw => ?_⟩, ?_⟩
  · rw [hloc w]
    simp only [hw, if_true]
  · rw [hloc w]
    simp only [hw, if_false]
  · rintro R ⟨-, hR1, hR0⟩
    apply eq_of_localization_eq
    intro w
    rw [hloc w]
    by_cases hw : w ∈ S
    · simp only [hw, if_true]
      exact hR1 w hw
    · simp only [hw, if_false]
      exact hR0 w hw
end Formalism.DivisionValues
