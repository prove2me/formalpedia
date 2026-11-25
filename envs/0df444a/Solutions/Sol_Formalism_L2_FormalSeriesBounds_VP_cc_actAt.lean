-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_actAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:26.507246+00:00
-- url     : https://prove2.me/submissions/385316c2-2dd6-456d-adc0-11ef065083b1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (i : Fin dd) : MvPowerSeries.constantCoeff (actAt Y x a i) = 0 := by
  unfold actAt
  exact VP.cc_subst (fun q : Fin 1 × Fin dd => ha q.2) (Y.B.A.const x i)
end Formalism.L2.FormalSeriesBounds.VP
