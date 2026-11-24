-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.rdV_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:38:06.19354+00:00
-- url     : https://prove2.me/submissions/090a7527-bf6d-4860-8c78-7e82fc8abdf7

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_pat_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_dag_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_exp_mem_nlev
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hasDerivAt_psi

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (l : Fin r) (D : Set (Mx k r)) (f : Mx k r → E) (hR : RightEq k r z l.castSucc D f)
    (g : Mx k r) (hg : g ∈ Glev k r l.castSucc ∩ D) (X : Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X f g = (ell k r z X - star (ell k r z X)) • f g := by
  have hfun : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z cStd (NormedSpace.exp ((t : ℂ) • X)) • f g := by
    funext t
    apply hR g hg
    apply exp_mem_nlev (pat_smul _ hX)
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hfun]
  exact ((hasDerivAt_psi z hz X).smul_const (f g)).deriv
end Formalism.FourierDecayAlt.Q.QRR
