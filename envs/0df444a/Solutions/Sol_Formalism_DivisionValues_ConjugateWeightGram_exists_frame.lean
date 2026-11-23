-- Prove2me | solution 1 for Formalism.DivisionValues.ConjugateWeightGram.exists_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:45.609868+00:00
-- url     : https://prove2.me/submissions/cd05bfa6-f047-4cb3-ba5b-503f9f668ef1

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral

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
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram
open StepBAux
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open scoped MatrixOrder
namespace Formalism.DivisionValues.ConjugateWeightGram
theorem _root_.solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosDef) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, IsUnit Y.det ∧ (Y⁻¹)ᴴ * Y⁻¹ = A := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
  have hB' : A = Bᴴ * B := by rw [hB, Matrix.star_eq_conjTranspose]
  have hdet : IsUnit B.det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [hB', Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv _ hdet, hB']
end Formalism.DivisionValues.ConjugateWeightGram
