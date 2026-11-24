-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.unitary_levi_det_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:58.907185+00:00
-- url     : https://prove2.me/submissions/18d9d712-b492-448b-b137-b1776328d986

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_unit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (g₁ : Mat k r') (hg : g₁ ∈ GV k r') : ‖g₁.det‖ = 1 := by
  have hg' : g₁ᴴ * Hpk k r' * g₁ = Hpk k r' := hg
  have h1 := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have hH : (Hpk k r').det ≠ 0 := (Hpk_unit k r').ne_zero
  have h2 : star g₁.det * g₁.det = 1 := by
    have h3 : (star g₁.det * g₁.det - 1) * (Hpk k r').det = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h hH
  have h4 : ((‖g₁.det‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    exact h2
  have h5 : ‖g₁.det‖ ^ 2 = 1 := by exact_mod_cast h4
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5
end Formalism.FourierDecayAlt.P.B2x8
