-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.WB.s_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:41.743197+00:00
-- url     : https://prove2.me/submissions/090e6075-0f1a-44aa-a7c9-f0c309aee878

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_WB_q_polynomial_next_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.WB
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx6.WB
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) :
    (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) - ∑ i ∈ Icc 1 (P.k - 1), rc P π i =
      1 + 2 * (aC P π : ℂ) := by
  rw [q_polynomial_next_coeff]
  have e1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) + (P.k : ℂ) := by
    rw [Finset.sum_congr rfl (fun i _ => (by ring : (1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ)) =
      ((P.u i : ℂ) + P.u' i) + 1)), Finset.sum_add_distrib]
    simp
  have e2 : ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) = ∑ i ∈ Icc 1 (P.k - 1), rc P π i + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [e1, e2]
  unfold aC rc
  push_cast
  ring
end Formalism.FourierDecayAlt.P.Mx6.WB
