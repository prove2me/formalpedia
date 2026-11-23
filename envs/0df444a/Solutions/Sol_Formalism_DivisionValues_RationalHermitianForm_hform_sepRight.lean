-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.hform_sepRight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:59.178357+00:00
-- url     : https://prove2.me/submissions/1377b7ba-640c-493f-ad73-af8d62f6b254

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_single

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hdet : H.det ≠ 0) :
    (hform H).SeparatingRight := by
  intro y hy
  have h1 : H *ᵥ y = 0 := funext fun i => by rw [← hform_single]; exact hy _
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
end Formalism.DivisionValues.RationalHermitianForm
