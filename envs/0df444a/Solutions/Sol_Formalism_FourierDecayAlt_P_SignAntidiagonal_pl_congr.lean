-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.pl_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:55:43.430349+00:00
-- url     : https://prove2.me/submissions/4947a22b-fc76-454f-92f1-91702fd42ccc

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlMonoConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution {t : ℕ} {f g : ℂ → A} (h : ∀ u, f u = g u) (hf : PolyLe t f) : PolyLe t g := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun u => by rw [← h u]; exact hC u⟩
end Formalism.FourierDecayAlt.P.SignAntidiagonal
