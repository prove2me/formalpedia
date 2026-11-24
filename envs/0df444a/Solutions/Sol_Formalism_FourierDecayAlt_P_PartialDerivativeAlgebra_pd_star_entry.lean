-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_star_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:23:01.32179+00:00
-- url     : https://prove2.me/submissions/934851e3-09bb-4d17-9d72-8311c05eb36e

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
theorem _root_.solution (i j : Fin N) : U.IsPolyDeg 1 (fun g : Matrix (Fin N) (Fin N) ℂ => star (g i j)) := by
  refine ⟨MvPolynomial.X (Sum.inr (i, j)), ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_X _).le
  · simp
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
