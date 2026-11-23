-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.lin_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:20.543464+00:00
-- url     : https://prove2.me/submissions/21557c8d-6ab6-47ba-aa8a-88dd67521644

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
omit L
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution (n z S : A) (c c' e : ℂ) (hn : n * S = S * n + algebraMap ℂ A e * (z * S))
    (hz : z * S = S * z) (hc : c' = c + e) :
    (-n - algebraMap ℂ A c * z) * S = S * (-n - algebraMap ℂ A c' * z) := by
  calc (-n - algebraMap ℂ A c * z) * S = -(n * S) - algebraMap ℂ A c * (z * S) := by noncomm_ring
    _ = -(S * n + algebraMap ℂ A e * (S * z)) - algebraMap ℂ A c * (S * z) := by rw [hn, hz]
    _ = -(S * n) - (algebraMap ℂ A e * S) * z - (algebraMap ℂ A c * S) * z := by noncomm_ring
    _ = -(S * n) - (S * algebraMap ℂ A e) * z - (S * algebraMap ℂ A c) * z := by
        rw [Algebra.commutes e S, Algebra.commutes c S]
    _ = S * (-n - algebraMap ℂ A (c + e) * z) := by rw [map_add]; noncomm_ring
    _ = _ := by rw [hc]
end Formalism.FourierDecayAlt.P.RuleSS
