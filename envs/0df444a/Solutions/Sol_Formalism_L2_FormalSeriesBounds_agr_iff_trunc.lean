-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.agr_iff_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:14:58.116574+00:00
-- url     : https://prove2.me/submissions/10449a62-8ded-4b0d-a116-aff9f4e07a2d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {τ : Type} [Finite τ] (k : ℕ) (f g : MvPowerSeries τ C) :
    Agr k f g ↔ MvPowerSeries.truncTotal k f = MvPowerSeries.truncTotal k g := by
  constructor
  · intro h
    ext e
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with he
    · exact h e he
    · rfl
  · intro h e he
    have h2 := congrArg (MvPolynomial.coeff e) h
    rwa [MvPowerSeries.coeff_truncTotal _ he, MvPowerSeries.coeff_truncTotal _ he] at h2
end Formalism.L2.FormalSeriesBounds
