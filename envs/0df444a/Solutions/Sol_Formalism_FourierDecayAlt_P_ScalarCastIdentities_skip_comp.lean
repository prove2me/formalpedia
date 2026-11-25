-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.skip_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:10.189946+00:00
-- url     : https://prove2.me/submissions/20d7e60f-0a3c-47ec-8d8b-47334456b357

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_skip_succ_identity


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
theorem _root_.solution (t : ℕ) (q : Fin (t + 2)) (k : Fin (t + 1)) :
    (skip1 q ∘ k.succAbove : Fin t → Fin (t + 2)) = skip2 (min (skip1 q k) q) (max (skip1 q k) q) := by
  funext j
  apply Fin.ext
  rw [Function.comp, ← skip_succ_identity]
  simp only [skip1, skip2, Fin.coe_min, Fin.coe_max, apply_ite Fin.val]
  split_ifs <;> omega
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
