-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:15:49.035277+00:00
-- url     : https://prove2.me/submissions/73f6129d-dbf3-4fd3-bff6-dd95775d85de

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
theorem _root_.solution (c : ℂ) (d : ℕ) : U.IsPolyDeg (N := N) d (fun _ => c) := by
  refine ⟨MvPolynomial.C c, ?_, fun g => ?_⟩
  · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  · simp
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
