-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.comp_coordinate_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:57.908144+00:00
-- url     : https://prove2.me/submissions/89ed5de1-7693-4935-9e85-22ec44922457

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_eval_single_eq_subst


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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (φ : Pt C 1 dd) (g : Fin 2) (i : Fin dd) :
    comp1 φ (pt C (n := 2) dd g) i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (X (g, q.2) : PS C 2 dd)) (φ i) := by
  show ev ![pt C (n := 2) dd g] (φ i) = _
  rw [eval_single_eq_subst]
  rfl
end Formalism.L2.FormalSeriesBounds
