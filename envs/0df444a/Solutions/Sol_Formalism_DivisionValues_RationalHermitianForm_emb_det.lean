-- Prove2me | solution 1 for Formalism.DivisionValues.RationalHermitianForm.emb_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:37.100311+00:00
-- url     : https://prove2.me/submissions/0c72d488-0926-4a6e-a191-bee065547d89

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
theorem _root_.solution {K0 : Subfield K} {n : ℕ} {H : Matrix (Fin n) (Fin n) K}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} (hR : IsRatHerm K0 H X) (v : InfinitePlace K) :
    v.embedding H.det = star ((X v)⁻¹.det) * (X v)⁻¹.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← (hR.2 v).2, Matrix.det_mul,
    Matrix.det_conjTranspose]
end Formalism.DivisionValues.RationalHermitianForm
