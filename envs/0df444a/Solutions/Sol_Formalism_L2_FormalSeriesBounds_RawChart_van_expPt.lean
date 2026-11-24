-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.van_expPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:32:26.091101+00:00
-- url     : https://prove2.me/submissions/d856ced0-79b2-44bb-8273-d39248b1e5c6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_van_lin
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
namespace Formalism.L2.FormalSeriesBounds.RawChart
theorem _root_.solution (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2) (x : κ) :
    Van {w : WV I | w.1 = g} (X.expPt g x) := by
  unfold expPt
  refine Van.subst Set.univ (fun i => (van_lin g _).const) (fun i _ => van_lin g _) ?_
  intro e he
  have he0 : e = 0 := by
    rw [← Finsupp.support_eq_empty]
    exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
  rw [he0, coeff_zero_eq_constantCoeff_apply]
  exact hex x
end Formalism.L2.FormalSeriesBounds.RawChart
