-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.le_of_forall_localized_le_of_not_isField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:03.225354+00:00
-- url     : https://prove2.me/submissions/d4a251d5-d82c-47df-890f-36414cc3c770

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_lg

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
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (hR : ¬ IsField R) (A B : Submodule R V)
    (h : ∀ w : HeightOneSpectrum R, localization₂ w.asIdeal A ≤ localization₂ w.asIdeal B) : A ≤ B :=
  fun x hx => lg hR B x fun w => h w ⟨1, w.asIdeal.primeCompl.one_mem, by simpa using hx⟩
end Formalism.DivisionValues.GluingInclusion
