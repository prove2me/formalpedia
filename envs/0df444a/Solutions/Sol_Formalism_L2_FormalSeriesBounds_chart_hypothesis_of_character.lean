-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.chart_hypothesis_of_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:47:53.333252+00:00
-- url     : https://prove2.me/submissions/5c8b65f4-055f-448d-bc3f-95bae156fa22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_chSt_of_char

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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hG : CharGermSt) (h : CharacterHypothesisCharts Xo c) : CharacterHypothesisAllCharts Xo c := by
  intro hs T io y C3 C _ _ V ι hemb k Y hbc Orb d _ lab ha hg hrk o Hc
  exact chSt_of_char hG Y _ (h hs T io y C3 C V ι hemb k Y hbc Orb d lab ha hg hrk o) Hc
end Formalism.L2.FormalSeriesBounds
