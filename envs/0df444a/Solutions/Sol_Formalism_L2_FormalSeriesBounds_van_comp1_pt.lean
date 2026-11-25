-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.van_comp1_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:20:02.796236+00:00
-- url     : https://prove2.me/submissions/4826044a-568e-43d5-95e4-5ffc57392fc3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_comp_coordinate_point
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_univ


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
theorem _root_.solution {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) (g : Fin 2) (i : Fin dd) :
    Van (Tg dd g) (comp1 φ (pt C (n := 2) dd g) i) := by
  rw [comp_coordinate_point]
  exact Van.subst Set.univ (fun _ => constantCoeff_X _) (fun q _ => van_X (show (g, q.2) ∈ Tg dd g from rfl))
    (van_univ (hφ i))
end Formalism.L2.FormalSeriesBounds
