-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.hLf_leaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:57:04.078973+00:00
-- url     : https://prove2.me/submissions/d516b8c8-f99f-4878-9ded-a5663505c8f7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDefs
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
variable {X}
variable (X)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : MvPowerSeries.coeff μ (X.hLf g a a') ≠ 0) : ∀ w ∈ μ.support, X.OnLf g a a' w := by
  by_contra hn
  apply h
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [if_neg hn]
end Formalism.L2.FormalSeriesBounds.RawChart
