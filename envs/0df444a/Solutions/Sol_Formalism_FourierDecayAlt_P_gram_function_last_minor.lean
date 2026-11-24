-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_function_last_minor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:44:00.474012+00:00
-- url     : https://prove2.me/submissions/ef339013-3c42-496f-8144-740c205c0347

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PartialDerivativeAlgebra
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.GfDlast := by
  intro k r z z' hz hz' g ε hε
  unfold Gf at hε
  have h0 : 0 ≤ Tz k r z * Tz k r z' * Complex.normSq (Dmin k r z z' g ⟨r, by omega⟩) :=
    mul_nonneg (mul_nonneg hz hz') (Complex.normSq_nonneg _)
  linarith
end Formalism.FourierDecayAlt.P
