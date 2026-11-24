-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LeftMultiplicationRule.hasDerivAt_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:49:33.503422+00:00
-- url     : https://prove2.me/submissions/1fdf00ec-f5c3-4719-ac2d-53682e64bc8c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_MulApplyS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_ReflectionColumnDualIsotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftPhaseRule_HasDerivAtPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
theorem _root_.solution (A B : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (((cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re : ℝ) : ℂ)))
      (Complex.I * (((cStd * A).re : ℝ) : ℂ)) 0 := by
  have e : ∀ t : ℝ, (cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B)).re = t * (cStd * A).re + t ^ 2 * (cStd * B).re := by
    intro t
    have h : cStd * ((t : ℂ) * A + (t : ℂ) ^ 2 * B) = (t : ℂ) * (cStd * A) + ((t ^ 2 : ℝ) : ℂ) * (cStd * B) := by
      push_cast; ring
    rw [h, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  simp_rw [e]
  have ha : HasDerivAt (fun t : ℝ => t * (cStd * A).re) (1 * (cStd * A).re) 0 :=
    (hasDerivAt_id' (0 : ℝ)).mul_const _
  have hb : HasDerivAt (fun t : ℝ => t ^ 2 * (cStd * B).re) (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * (cStd * B).re) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  have h1 : HasDerivAt (fun t : ℝ => t * (cStd * A).re + t ^ 2 * (cStd * B).re) ((cStd * A).re) 0 :=
    (ha.add hb).congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul Complex.I).cexp
  exact h2.congr_deriv (by simp)
end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
