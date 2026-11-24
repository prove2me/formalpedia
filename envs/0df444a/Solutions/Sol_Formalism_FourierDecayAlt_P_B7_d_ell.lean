-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.d_ell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:36:16.769917+00:00
-- url     : https://prove2.me/submissions/28c56d72-be7a-4585-918a-e2511952f270

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_d_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (t : ℝ) (ht : t ≠ 0) (n : Mat k r) :
    ell k r z (aDil k r t * n * (aDil k r t)⁻¹) = (t : ℂ) * ell k r z n := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos h, d_conj_apply t ht]
    have e1 : d_dg k r t (eI k r a) = ((t ^ (r - a.val) : ℝ) : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]; rfl
    have e2 : d_dg k r t⁻¹ (eI k r ⟨a.val + 1, h⟩) = (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]; rfl
    rw [e1, e2]
    have e3 : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have e4 : ((t ^ (r - a.val) : ℝ) : ℂ) * (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, e3, pow_succ, mul_assoc, mul_comm t, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ ht, one_pow, one_mul]
    calc _ = (((t ^ (r - a.val) : ℝ) : ℂ) * (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ)) *
          n (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by ring
      _ = _ := by rw [e4]
  · rw [dif_neg h, dif_neg h]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d_conj_apply t ht]
    have e1 : d_dg k r t (eI k r a) = (t : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]
      have : r - (eI k r a).val = 1 := by simp only [eI]; omega
      rw [this, pow_one]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj]; simp
    · have e2 : d_dg k r t⁻¹ j = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      rw [e1, e2]; ring
end Formalism.FourierDecayAlt.P.B7
