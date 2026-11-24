-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.hasDerivAt_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:20:35.59284+00:00
-- url     : https://prove2.me/submissions/7507e2f1-b167-44c0-849d-5fd6c631fa54

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_ell_one
import Theorems.Thm_Formalism_REAL_hasDerivAt_matrix_exp_smul_at_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • X)))
      (ell k r z X - star (ell k r z X)) 0 := by
  have hE := Formalism.REAL.hasDerivAt_matrix_exp_smul_at_zero X
  have hL : HasDerivAt (fun t : ℝ => ell k r z (NormedSpace.exp ((t : ℂ) • X))) (ell k r z X) 0 := by
    have := (LinearMap.toContinuousLinearMap (ellL k r z)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hE
    exact this
  have hre : HasDerivAt (fun t : ℝ => (cStd * ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
      (cStd * ell k r z X).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hL.const_mul cStd)
    exact this
  have h1 := ((hre.ofReal_comp).const_mul Complex.I).cexp
  unfold psi
  convert h1 using 1
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one z hz, mul_zero, Complex.zero_re,
    Complex.exp_zero, one_mul]
  unfold cStd
  rw [Complex.star_def]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
end Formalism.FourierDecayAlt.Q.QRR
