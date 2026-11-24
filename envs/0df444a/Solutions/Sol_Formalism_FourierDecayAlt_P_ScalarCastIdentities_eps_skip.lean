-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.eps_skip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:51.672411+00:00
-- url     : https://prove2.me/submissions/6fc9c97b-280a-4967-8b4b-61deb4b73e1c

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A)
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution (t : ℕ) (q : Fin (t + 1)) (k : Fin t) :
    ((eps (skip1 q k) q : ℤ) : ℂ) * (-1 : ℂ) ^ ((skip1 q k : Fin (t + 1)) : ℕ) = (-1 : ℂ) ^ (k : ℕ) := by
  by_cases h : k.val < q.val
  · have h1 : ((skip1 q k : Fin (t + 1)) : ℕ) = k.val := by simp only [skip1, apply_ite Fin.val]; rw [if_pos h]
    rw [eps, h1, if_pos h]
    simp
  · have h1 : ((skip1 q k : Fin (t + 1)) : ℕ) = k.val + 1 := by simp only [skip1, apply_ite Fin.val]; rw [if_neg h]
    rw [eps, h1, if_neg (by omega)]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
