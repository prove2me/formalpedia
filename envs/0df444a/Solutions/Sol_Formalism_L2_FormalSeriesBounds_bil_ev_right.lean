-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.bil_ev_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:19.896843+00:00
-- url     : https://prove2.me/submissions/af63ccc8-92a9-4ac8-91cc-0c5056d95dcf

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_ev_right

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
variable {h : PS C 2 dd}
  (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
  {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0)
include hh hφ
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (w v : Fin dd → C) :
    bil (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) w v = bil h w (linAct φ v) := by
  unfold bil linAct
  simp only [coeff_ev_right hh hφ, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring
end Formalism.L2.FormalSeriesBounds
