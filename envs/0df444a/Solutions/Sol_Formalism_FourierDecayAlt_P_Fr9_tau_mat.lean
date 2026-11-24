-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.tau_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:03.30086+00:00
-- url     : https://prove2.me/submissions/0b0f1e36-6fe5-48b8-80b1-e48f0401eed6

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mk2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {B : Type*} [Ring B] [Algebra ℂ B] {zbi zg m τ t12 : B} {d : ℂ}
    (h1 : Commute zbi τ) (h2 : Commute zg τ) (hk : d • (m * τ - τ * m) = t12 - τ * m) :
    !![zbi, 0; zg * m, zg] * !![d • τ, 0; -t12, (d - 1) • τ] =
      !![d • τ, 0; 0, (d - 1) • τ] * !![zbi, 0; zg * m, zg] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine mk2 ?_ ?_ ?_ ?_
  · rw [zero_mul, zero_mul, add_zero, add_zero, mul_smul_comm, smul_mul_assoc, h1.eq]
  · simp
  · have e : d • (m * τ) - t12 = (d - 1) • (τ * m) := by
      rw [smul_sub] at hk
      rw [sub_smul, one_smul]
      rw [sub_eq_iff_eq_add] at hk
      rw [hk]; abel
    rw [zero_mul, zero_add, mul_assoc, mul_smul_comm, mul_neg, ← sub_eq_add_neg, ← mul_sub, e, mul_smul_comm,
      smul_mul_assoc, ← mul_assoc, ← mul_assoc, h2.eq]
  · rw [mul_zero, zero_mul, zero_add, zero_add, mul_smul_comm, smul_mul_assoc, h2.eq]
end Formalism.FourierDecayAlt.P.Fr9
