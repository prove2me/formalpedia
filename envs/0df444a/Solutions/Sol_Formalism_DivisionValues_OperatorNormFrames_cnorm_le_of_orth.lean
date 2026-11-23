-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.cnorm_le_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:16.824923+00:00
-- url     : https://prove2.me/submissions/453ece86-e579-43d9-aa03-7fa5ff96dc83

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_nonneg
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_star_dot_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open OperatorNormFrames
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {n : ℕ} (p q : Fin n → ℂ) (h : star p ⬝ᵥ q = 0) :
    Formalism.HermitianLatticesTheory.cnorm p ≤ Formalism.HermitianLatticesTheory.cnorm (p + q) := by
  have h2 : star q ⬝ᵥ p = 0 := by
    have e : star q ⬝ᵥ p = star (star p ⬝ᵥ q) := by
      first
        | simp [dotProduct, mul_comm]
        | simp [Matrix.dotProduct, mul_comm]
    rw [e, h, star_zero]
  have key : ((Formalism.HermitianLatticesTheory.cnorm (p + q) ^ 2 : ℝ) : ℂ) =
      ((Formalism.HermitianLatticesTheory.cnorm p ^ 2 + Formalism.HermitianLatticesTheory.cnorm q ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, ← star_dot_self, ← star_dot_self, ← star_dot_self, star_add]
    first
      | rw [add_dotProduct, dotProduct_add, dotProduct_add, h, h2]
      | rw [Matrix.add_dotProduct, Matrix.dotProduct_add, Matrix.dotProduct_add, h, h2]
    ring
  have key' := Complex.ofReal_injective key
  nlinarith [cnorm_nonneg p, cnorm_nonneg (p + q), sq_nonneg (Formalism.HermitianLatticesTheory.cnorm q)]
end Formalism.DivisionValues.OperatorNormFrames
