-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.exists_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:52:00.278834+00:00
-- url     : https://prove2.me/submissions/6979d33e-5938-4a55-9699-414511397e88

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution {n : ℕ} (a : Fin (n + 1)) (h : a ≠ Fin.last n) : ∃ a' : Fin n, a = a'.castSucc := by
  first
  | exact ⟨a.castPred h, (Fin.castSucc_castPred a h).symm⟩
  | (obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr h; exact ⟨j, hj.symm⟩)
end Formalism.FourierDecayAlt.P.ClosureOperators
