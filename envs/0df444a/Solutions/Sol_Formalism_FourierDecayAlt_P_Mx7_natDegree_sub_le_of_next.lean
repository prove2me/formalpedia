-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.natDegree_sub_le_of_next
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:59.323259+00:00
-- url     : https://prove2.me/submissions/dc7dd9a1-bfbc-406b-ab11-896d4cf7c179

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

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
theorem _root_.solution (p1 p2 : ℂ[X]) (N : ℕ) (h1 : p1.Monic) (h2 : p2.Monic)
    (d1 : p1.natDegree = N + 2) (d2 : p2.natDegree = N + 2) (hn : p1.nextCoeff = p2.nextCoeff) :
    (p1 - p2).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_sub]
  rcases Nat.lt_or_ge (N + 2) m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  · have : m = N + 1 ∨ m = N + 2 := by omega
    rcases this with rfl | rfl
    · rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), d1, d2] at hn
      have e : N + 2 - 1 = N + 1 := by omega
      rw [e] at hn
      rw [hn, sub_self]
    · have a1 : p1.coeff (N + 2) = 1 := by rw [← d1]; exact h1.coeff_natDegree
      have a2 : p2.coeff (N + 2) = 1 := by rw [← d2]; exact h2.coeff_natDegree
      rw [a1, a2, sub_self]
end Formalism.FourierDecayAlt.P.Mx7
