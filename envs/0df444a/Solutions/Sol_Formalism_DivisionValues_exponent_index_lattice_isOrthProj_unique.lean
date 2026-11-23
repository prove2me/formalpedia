-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.isOrthProj_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:16.843408+00:00
-- url     : https://prove2.me/submissions/ffcce855-b25c-482e-bb07-6cb082e70356

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
theorem _root_.solution {n d : ℕ} {H : Matrix (Fin n) (Fin n) K} {E : Matrix (Fin n) (Fin d) K}
    {Pr : Matrix (Fin d) (Fin n) K} (hZ : IsUnit (Eᴴ * H * E).det) (hO : IsOrthProj H E Pr) :
    Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H) := by
  have h2 : Eᴴ * H = Eᴴ * H * E * Pr := by
    have h := hO.2
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc (Eᴴ * H) E Pr] at h
    exact h
  calc Pr = (Eᴴ * H * E)⁻¹ * (Eᴴ * H * E) * Pr := by rw [Matrix.nonsing_inv_mul _ hZ, Matrix.one_mul]
    _ = (Eᴴ * H * E)⁻¹ * (Eᴴ * H) := by rw [Matrix.mul_assoc (Eᴴ * H * E)⁻¹ (Eᴴ * H * E) Pr, ← h2]
end Formalism.DivisionValues.exponent_index_lattice
