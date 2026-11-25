-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.nuLocC_le_nval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:23.39563+00:00
-- url     : https://prove2.me/submissions/ca859141-9205-4081-ae87-3f834a47f50a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc

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
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (C3 : IntChart T io y) (e k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (P : MvPolynomial (LtN Dw n) T.Fr) (hP : P ∈ FFV (Dw := Dw) T a n) (f : PS T.Fr n (chD C3.ch)) (hf : IsIntPS T f) :
    nuLocC C3 e k a n ≤ nval T.V e (chartDerivativeCoefficient C3 k n f P) := by
  unfold nuLocC chartDerivativeCoefficient
  exact le_trans (iInf₂_le P hP) (iInf₂_le f hf)
end Formalism.L2.FormalSeriesBounds
