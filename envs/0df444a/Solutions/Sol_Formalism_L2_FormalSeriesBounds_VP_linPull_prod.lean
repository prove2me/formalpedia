-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.linPull_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:02:15.527806+00:00
-- url     : https://prove2.me/submissions/4b6df341-9d4d-4e12-a459-7c69fe11d46e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_linPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_prod


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
theorem _root_.solution {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by
  unfold linPull
  exact VP.subst_prod (cc_linPt Y M) s F
end Formalism.L2.FormalSeriesBounds.VP
