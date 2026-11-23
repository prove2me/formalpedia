-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:25.649908+00:00
-- url     : https://prove2.me/submissions/babf1069-edeb-4f62-9d82-a6aa9825aa3c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_locS_top


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
theorem _root_.solution (A B : Submodule R V) (hA : A.FG) (hB : Submodule.span K (B : Set V) = ⊤) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ A, d • x ∈ B := by
  obtain ⟨d, hd, h⟩ := indexBasic_denom (nonZeroDivisors R) A B hA
    (by rw [indexBasic_locS_top (K := K) B hB]; exact le_top)
  exact ⟨d, nonZeroDivisors.ne_zero hd, h⟩
end Formalism.DivisionValues.GluingInclusion
