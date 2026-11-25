-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.linPull_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:21.584497+00:00
-- url     : https://prove2.me/submissions/185b0dbc-4b71-4c9c-92e4-481409f95043

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_linPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_mul


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (F G : PS C n dd) : linPull Y M (F * G) = linPull Y M F * linPull Y M G := by
  unfold linPull
  exact VP.subst_mul (cc_linPt Y M) F G
end Formalism.L2.FormalSeriesBounds.VP
