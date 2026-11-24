-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:15:49.373922+00:00
-- url     : https://prove2.me/submissions/3b919992-995d-4d20-9c73-e032192f2fa3

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
theorem _root_.solution {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by
  obtain ⟨q, hq, hP⟩ := h
  exact ⟨q, hq.trans hab, hP⟩
end Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
