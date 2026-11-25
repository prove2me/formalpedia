-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FBChart.rawSelf_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:30:57.395787+00:00
-- url     : https://prove2.me/submissions/adc25617-d71c-4510-9ec1-9f7a7955cfe0

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePAxesSelfSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePCartSelfSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inCol_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_inCol_lin
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_uncurry_X


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
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
namespace Formalism.L2.FormalSeriesBounds
namespace FBChart
theorem _root_.solution (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl
end FBChart
end Formalism.L2.FormalSeriesBounds
