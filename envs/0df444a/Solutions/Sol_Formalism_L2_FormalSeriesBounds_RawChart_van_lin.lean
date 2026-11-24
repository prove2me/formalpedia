-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.van_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:16.653493+00:00
-- url     : https://prove2.me/submissions/76550526-427e-4744-9d90-61d32b23d81c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
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
theorem _root_.solution (g : Fin 2) (b : I g → C) :
    Van {w : WV I | w.1 = g} (∑ c : I g, b c • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) := by
  intro ν hν
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [coeff_smul, coeff_X, if_neg, mul_zero]
  intro h
  exact hν ⟨g, c⟩ (by rw [h]; simp) rfl
end Formalism.L2.FormalSeriesBounds.RawChart
