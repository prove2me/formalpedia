-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.mapAt_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:03:49.308831+00:00
-- url     : https://prove2.me/submissions/815e31f2-dd64-439e-b52c-d453c30d7fe3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_comp_eq_map_at
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_GoodPt_act
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst


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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) (x : O)
    (hc : comp1 ε (Y.B.A.act x) = comp1 (Y.B.A.act x) ε) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mapAt ε (actAt Y x a) = actAt Y x (mapAt ε a) := by
  unfold actAt
  have hA : ∀ i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := fun i => Y.B.A.2 x i
  rw [comp_eq_map_at, comp_eq_map_at] at hc
  funext i
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  have hAs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => Y.B.A.act x q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hA q.2)
  have hεs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => ε q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hε q.2)
  have hci : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => Y.B.A.act x q.2) (ε i) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => ε q.2) (Y.B.A.act x i) := congrFun hc i
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      MvPowerSeries.subst (fun q' : Fin 1 × Fin dd => a q'.2) (Y.B.A.act x q.2)) (ε i) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin dd =>
      MvPowerSeries.subst (fun q' : Fin 1 × Fin dd => a q'.2) (ε q.2)) (Y.B.A.act x i)
  rw [← MvPowerSeries.subst_comp_subst_apply hAs hb (ε i),
    ← MvPowerSeries.subst_comp_subst_apply hεs hb (Y.B.A.act x i), hci]
end Formalism.L2.FormalSeriesBounds.VP
