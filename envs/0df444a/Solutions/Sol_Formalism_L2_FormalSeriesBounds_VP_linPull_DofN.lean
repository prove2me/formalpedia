-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.linPull_DofN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:39.839272+00:00
-- url     : https://prove2.me/submissions/ef91e9bf-d52b-4225-a140-215824fb4b3c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_linPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_smul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_subst_sum


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
theorem _root_.solution (b : Fin n) (u : Fin dd → C) (F : PS C n dd) :
    linPull Y M (DofN (Y.B.FK C) b u F) =
      ∑ j, (∑ i, MvPowerSeries.C (u i) * RR Y M b i j) * linPull Y M (MvPowerSeries.pderiv C (b, j) F) := by
  unfold DofN
  simp only [← MvPowerSeries.smul_eq_C_mul]
  simp only [linPull, RR, VP.subst_sum (cc_linPt Y M), VP.subst_mul (cc_linPt Y M), VP.subst_smul (cc_linPt Y M)]
end Formalism.L2.FormalSeriesBounds.VP
