-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.jet_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:04.368175+00:00
-- url     : https://prove2.me/submissions/34eda3a5-14d4-4b84-9c32-a902837178ee

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
theorem _root_.solution {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by
  simp only [jetAt0, map_sum, Finset.mul_sum]
  exact Finset.sum_comm
end Formalism.L2.FormalSeriesBounds
