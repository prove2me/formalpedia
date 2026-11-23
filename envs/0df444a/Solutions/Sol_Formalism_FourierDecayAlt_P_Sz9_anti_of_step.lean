-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz9.anti_of_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:54.892743+00:00
-- url     : https://prove2.me/submissions/da49602d-8301-4899-8f40-941a69e8ef34

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SixteenMulLeTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz9
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz9
theorem _root_.solution (p : ℕ) (x : ℕ → ℝ) (h : ∀ i, 1 ≤ i → i < p → x (i + 1) < x i) :
    ∀ s t, 1 ≤ s → s < t → t ≤ p → x t < x s := by
  intro s t hs hst htp
  obtain ⟨d, rfl⟩ : ∃ d, t = s + 1 + d := ⟨t - (s + 1), by omega⟩
  induction d with
  | zero => simpa using h s hs (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := h (s + 1 + d) (by omega) (by omega)
    have e : s + 1 + (d + 1) = s + 1 + d + 1 := by omega
    rw [e]
    linarith
end Formalism.FourierDecayAlt.P.Sz9
