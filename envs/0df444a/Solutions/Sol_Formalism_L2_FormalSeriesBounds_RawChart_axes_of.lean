-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RawChart.axes_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:11.720978+00:00
-- url     : https://prove2.me/submissions/9efdac15-61ea-4d11-a847-53b7ab9d136d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_van_hRow
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
theorem _root_.solution (hex : ∀ x, constantCoeff (X.ex x) = 0)
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) : X.AxesSt := by
  intro μ h
  rcases h with h | h
  · exact X.van_hRow hex 1 (hh 1) μ fun w hw hw1 => by
      have h0 := h w hw
      have h1 : w.1 = 1 := hw1
      rw [h0] at h1
      exact absurd h1 (by decide)
  · exact X.van_hRow hex 0 (hh 0) μ fun w hw hw0 => by
      have h1 := h w hw
      have h0 : w.1 = 0 := hw0
      rw [h1] at h0
      exact absurd h0 (by decide)
end Formalism.L2.FormalSeriesBounds.RawChart
