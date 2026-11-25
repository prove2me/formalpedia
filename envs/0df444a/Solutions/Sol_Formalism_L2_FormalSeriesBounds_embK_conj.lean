-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.embK_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:01.312276+00:00
-- url     : https://prove2.me/submissions/5aa2379b-4f7e-4935-81d0-1d205deb6dac

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab

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
theorem _root_.solution (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]
end Formalism.L2.FormalSeriesBounds
