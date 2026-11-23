-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.herm_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:18.611653+00:00
-- url     : https://prove2.me/submissions/072a073e-15a7-43f1-b3e9-26a76a7a0bb2

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

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
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} (hH : Hᴴ = H)
    (E : Matrix (Fin n) (Fin d) K) : (Eᴴ * H * E)ᴴ = Eᴴ * H * E := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
end Formalism.DivisionValues.exponent_index_lattice
