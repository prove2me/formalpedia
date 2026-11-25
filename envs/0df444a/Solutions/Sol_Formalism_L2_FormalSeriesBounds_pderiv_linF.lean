-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.pderiv_linF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:39:53.254613+00:00
-- url     : https://prove2.me/submissions/0adc2032-3047-4e04-bf0e-97acb290ea38

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (lam : τ → K) (w : τ) : pderiv K w (linF lam) = C (lam w) := by
  classical
  rw [linF, map_sum]
  simp only [Derivation.map_smul, pderiv_X]
  rw [Finset.sum_eq_single w]
  · simp [MvPowerSeries.smul_eq_C_mul]
  · intro b _ hb
    simp [hb]
  · simp
end Formalism.L2.FormalSeriesBounds
