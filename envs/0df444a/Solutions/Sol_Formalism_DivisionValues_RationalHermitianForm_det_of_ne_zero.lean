-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.det_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:08.034158+00:00
-- url     : https://prove2.me/submissions/239ac365-0ea7-45b8-bc42-fade0dc92e07

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.RationalHermitianForm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.RationalHermitianForm
theorem _root_.solution {d : ℕ} {f : Fin d → Fin d → K} (hf : LinearIndependent K f) :
    (Matrix.of f)ᵀ.det ≠ 0 := by
  rw [Matrix.det_transpose]
  have h1 : IsUnit (Matrix.of f) := Matrix.linearIndependent_rows_iff_isUnit.mp hf
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h1).ne_zero
end Formalism.DivisionValues.RationalHermitianForm
