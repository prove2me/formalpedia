-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:41.101682+00:00
-- url     : https://prove2.me/submissions/5596b135-6bac-4592-bc7c-e77cc2c63ec6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMJet

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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)
variable {C : Type} [Field C] {σ τ : Type}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (P : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 P (a • G) = a * jetAt0 P G := by
  simp only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring
end Formalism.L2.FormalSeriesBounds
