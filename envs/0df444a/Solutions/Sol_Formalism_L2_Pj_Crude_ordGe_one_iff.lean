-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.ordGe_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:24.320846+00:00
-- url     : https://prove2.me/submissions/94ab17a0-7fff-4f93-bd30-9e24c7c774bb

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
theorem _root_.solution (f : PS k n d) : OrdGe 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by simp)
    first
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using h0
  · intro h m hm
    have hm0 : m = 0 := by
      have hd : m.degree = 0 := by omega
      first
        | exact (Finsupp.degree_eq_zero_iff m).1 hd
        | exact Finsupp.degree_eq_zero_iff.1 hd
    subst hm0
    first
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using h
      | simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using h
end Formalism.L2.Pj.Crude
