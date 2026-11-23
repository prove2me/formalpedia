-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.modE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:02.993476+00:00
-- url     : https://prove2.me/submissions/e72672c9-6310-4c71-9c93-9d9ea1356c69

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_q_polynomial_next_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) :
    2 * (aC P π : ℂ) + 1 = (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ) -
      ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) := by
  rw [q_polynomial_next_coeff]
  have s1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      (P.k : ℂ) + ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) := by
    rw [Finset.sum_congr rfl (fun i _ => show ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      1 + ((P.u i : ℂ) + (P.u' i : ℂ)) by ring), Finset.sum_add_distrib]
    simp
  have s2 : ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) =
      (∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ)) + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [s1, s2]
  unfold aC
  push_cast
  ring
end Formalism.FourierDecayAlt.P.Mx7
