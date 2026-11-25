-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.axesFB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:10:40.549898+00:00
-- url     : https://prove2.me/submissions/9c83bcb1-8c0e-44a2-9c51-06355c8cd64d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_axes_of
import Theorems.Thm_P2M_Formalism_L2_FormalSeriesBounds_fin_two_eq_one_sub_of_ne__93512bbd28f7
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_of_ev_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_uncurry

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
theorem _root_.solution : AxesFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (un1 (Y.ex x)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const x
  · intro g
    show ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl
end Formalism.L2.FormalSeriesBounds
