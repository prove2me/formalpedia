-- Prove2me | solution 1 for Formalism.L2.Pj.valV_wchar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:52.690306+00:00
-- url     : https://prove2.me/submissions/7047b3b4-0722-4e22-b28b-7d3fd3fa9d96

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace Formalism.L2.Pj
theorem _root_.solution {T : CDVR} (e : Ix Dw → ℕ) (t : Ix Dw → T.Frˣ)
    (ht : ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1) : valV T.V (wchar e t) = 1 := by
  simp [wchar, map_prod, map_pow, ht]
end Formalism.L2.Pj
