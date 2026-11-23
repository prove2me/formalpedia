-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_ordGe_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:32.421736+00:00
-- url     : https://prove2.me/submissions/293fceb2-1593-4ab7-a71a-aca994b3882d

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
theorem _root_.solution {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (i : Fin n × Fin d) :
    OrdGe t (pderiv k i f) := by
  intro m hm
  unfold pderiv
  show coeff m (pderivFun i f) = 0
  unfold pderivFun
  have hz : coeff (m + Finsupp.single i 1) f = 0 := hf _ (by
    have e : (m + Finsupp.single i 1).degree = m.degree + 1 := by
      first
        | (rw [map_add, Finsupp.degree_single])
        | simp [Finsupp.degree_single]
        | (rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
           simp [Finset.sum_add_distrib, Finsupp.single_apply])
    omega)
  show coeff (m + Finsupp.single i 1) f * ((m i : k) + 1) = 0
  rw [hz, zero_mul]
end Formalism.L2.Pj.Crude
