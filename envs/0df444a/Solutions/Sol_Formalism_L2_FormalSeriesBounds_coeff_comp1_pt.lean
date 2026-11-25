-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_comp1_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:18.027209+00:00
-- url     : https://prove2.me/submissions/5cabb51a-50ec-430c-b310-e45da945034d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_comp_coordinate_point
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_subst_rename_inj


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
theorem _root_.solution (φ : Pt C 1 dd) (g : Fin 2) (i k : Fin dd) :
    coeff (Finsupp.single (g, k) 1) (comp1 φ (pt C (n := 2) dd g) i) =
      coeff (Finsupp.single ((0 : Fin 1), k) 1) (φ i) := by
  rw [comp_coordinate_point]
  have hinj : Function.Injective (fun q : Fin 1 × Fin dd => (g, q.2)) := fun x y h =>
    Prod.ext (Subsingleton.elim _ _) (Prod.mk.inj h).2
  have := coeff_subst_rename_inj (C := C) (fun q : Fin 1 × Fin dd => (g, q.2)) hinj (φ i)
    (Finsupp.single ((0 : Fin 1), k) 1)
  rw [Finsupp.mapDomain_single] at this
  exact this
end Formalism.L2.FormalSeriesBounds
