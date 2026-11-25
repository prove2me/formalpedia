-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.a3uvec_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:43:47.016251+00:00
-- url     : https://prove2.me/submissions/1ff5b7dc-2be7-4f72-af19-5b252afc865e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_embIntSt_holds


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
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  obtain ⟨⟨-, -, -, -, -, -, hu⟩, -⟩ := C3.gen
  rw [show chartUnitVectors C3 ℓ i = _ from hu ℓ i]
  exact embIntSt_holds T C V ι hι _
end Formalism.L2.FormalSeriesBounds
