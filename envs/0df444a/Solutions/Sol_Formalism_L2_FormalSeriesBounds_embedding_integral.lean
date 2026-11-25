-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.embedding_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:42:00.398853+00:00
-- url     : https://prove2.me/submissions/7a9ced48-d1ac-4c12-9c60-c1ee68b110e7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieLab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ge_of_isIntegral

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
theorem _root_.solution (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)
end Formalism.L2.FormalSeriesBounds
