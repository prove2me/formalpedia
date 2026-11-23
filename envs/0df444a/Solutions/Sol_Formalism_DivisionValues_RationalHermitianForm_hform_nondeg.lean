-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.hform_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:30.110434+00:00
-- url     : https://prove2.me/submissions/9e88ad34-611f-45ca-a79c-4a4ab134a995

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_sepRight

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hs : (hform H).IsSymm)
    (hdet : H.det ≠ 0) : (hform H).Nondegenerate := by
  have hsym : ∀ x y, starRingEnd K (hform H x y) = hform H y x := by
    intro x y
    first
      | exact hs x y
      | exact hs.eq x y
  refine ⟨fun x hx => hform_sepRight H hdet x (fun y => ?_), hform_sepRight H hdet⟩
  rw [← hsym x y, hx y, map_zero]
end Formalism.DivisionValues.RationalHermitianForm
