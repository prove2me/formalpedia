-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_into_dual_gluing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:04.677209+00:00
-- url     : https://prove2.me/submissions/4db1a719-b729-4cc6-a44b-f6cb5ac33240

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glueLat_spec
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq
import Theorems.Thm_P2M_Formalism_DivisionValues_GluingInclusion_matLat_lattice__63e4ff29817d
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_lattice


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
theorem _root_.solution : DivIntoDualGlue := by
  intro K _ _ _ D Tup μ0 μ hμ n M hM π hπ ι hι
  have hl : ∀ t, Submodule.IsLattice K (matLat (ι t) (matLat (π t) (M t))) := fun t =>
    StepBAux.matLat_lattice _ (hι t) _ (matLat_lattice' _ (hπ t) _ (hM t))
  obtain ⟨hlat, hloc⟩ := glueLat_spec (matLat (ι μ0) (matLat (π μ0) (M μ0)))
    (fun w => matLat (ι (μ w)) (matLat (π (μ w)) (M (μ w)))) (hl μ0) (fun w => hl (μ w))
    (hμ.subset (fun w hw h => hw (by rw [h])))
  exact ⟨_, ⟨hlat, hloc⟩, fun R hR => eq_of_localization_eq _ _ (fun w => by rw [hR.2 w, hloc w])⟩
end Formalism.DivisionValues
