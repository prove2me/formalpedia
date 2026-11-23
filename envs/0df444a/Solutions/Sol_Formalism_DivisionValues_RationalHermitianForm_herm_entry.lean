-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.herm_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:22:08.211373+00:00
-- url     : https://prove2.me/submissions/7a3370b7-1645-46d4-aa08-57f92ff839ff

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
theorem _root_.solution {K0 : Subfield K} (hcm : IsCMSub K0) {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) (i j : Fin n) :
    H j i = star (H i j) := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h1 := (hR.2 v).2
  have h2 : (H.map v.embedding)ᴴ = H.map v.embedding := by
    rw [← h1, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply] at h3
  apply v.embedding.injective
  rw [hcm v.embedding (H i j) (hR.1 i j), ← h3]
  simp
end Formalism.DivisionValues.RationalHermitianForm
