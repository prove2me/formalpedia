-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.embedding_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:46.763314+00:00
-- url     : https://prove2.me/submissions/ba0e64a7-b1ce-435a-ba3a-a8ae09ebbc86

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_embK_conj

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
theorem _root_.solution (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]
end Formalism.L2.FormalSeriesBounds
