-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.LogEx.linN_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:20:43.840329+00:00
-- url     : https://prove2.me/submissions/82f597dc-00b3-4842-bbfa-53f5c3bcd764

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePLogExSt

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.LogEx
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [CommRing C] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds.LogEx
theorem _root_.solution {f : Pt C 1 dd} (hf : LinN f) (i : Fin dd) : constantCoeff (f i) = 0 := by
  have h := hf i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h, MvPowerSeries.coeff_zero_X]
end Formalism.L2.FormalSeriesBounds.LogEx
