-- Prove2me | solution 1 for Formalism.L2.Pj.valV_algebraMap_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:16:50.490831+00:00
-- url     : https://prove2.me/submissions/071a0fe1-52ce-4a25-bc24-aa0695896ee7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameProofs

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
theorem _root_.solution (T : CDVR) {u : T.V} (hu : IsUnit u) :
    valV T.V (algebraMap T.V T.Fr u) = 1 := by
  unfold valV
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  intro h
  exact (IsDiscreteValuationRing.maximalIdeal T.V).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
end Formalism.L2.Pj
