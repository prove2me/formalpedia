-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.hform_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:26.724199+00:00
-- url     : https://prove2.me/submissions/7067a04b-ed6c-4f94-b1ef-82b4d1c1fe21

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Theorems.Thm_Formalism_DivisionValues_RationalHermitianForm_hform_apply

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
theorem _root_.solution {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (i : Fin n) (y : Fin n → K) :
    hform H (Pi.single i 1) y = (H *ᵥ y) i := by
  have hst : ∀ x : Fin n, star ((Pi.single i (1 : K) : Fin n → K) x) = (Pi.single i (1 : K) : Fin n → K) x := by
    intro x; rcases eq_or_ne x i with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hform_apply]
  simp only [hst]
  simp [Pi.single_apply, Matrix.mulVec, dotProduct]
end Formalism.DivisionValues.RationalHermitianForm
