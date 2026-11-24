-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_constCoeff_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:14:47.633805+00:00
-- url     : https://prove2.me/submissions/684d27c4-c8ae-4fd3-86b6-56153fe353af

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd

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
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution [Algebra ℚ k] (s : PS k n d) (hs : constantCoeff s = 0) :
    constantCoeff (FB.expS k s) = 1 := by
  have hs' : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst hs', finsum_eq_single _ 0]
  · simp [PowerSeries.coeff_exp]
  · intro e he
    rw [map_pow, hs, zero_pow he, smul_zero]
end Formalism.L2.Pj.Crude
