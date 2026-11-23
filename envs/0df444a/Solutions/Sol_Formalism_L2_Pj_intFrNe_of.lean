-- Prove2me | solution 1 for Formalism.L2.Pj.intFrNe_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:45.273489+00:00
-- url     : https://prove2.me/submissions/15196eff-b1e4-426c-8a99-e0d65a6c1005

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
theorem _root_.solution (hA : AlgPtLa Xo c) (hE : IntFrExt Xo c) :
    IntFrNe Xo c (fun _ _ y => IntFr.IsAlg y) := by
  intro la
  obtain ⟨T, io, e, hO, hF, x, hx⟩ := hA la
  obtain ⟨T', i, r, hr, hv, hF', y, hy⟩ := hE T io hF x hx
  unfold OverLa IntFr.IsAlg at *
  refine ⟨T', i.comp io, r * e, ⟨Nat.mul_pos hr hO.1, fun a => ?_⟩, y, hF'⟩
  rw [RingHom.comp_apply, hv, hO.2 a]
  push_cast
  ring
end Formalism.L2.Pj
