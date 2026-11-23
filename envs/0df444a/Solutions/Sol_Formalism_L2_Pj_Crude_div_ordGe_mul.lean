-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_ordGe_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:46.925798+00:00
-- url     : https://prove2.me/submissions/20210d3e-4445-4523-a63c-4c49841c1213

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {a b : ℕ} {f g : PS k n d} (hf : OrdGe a f) (hg : OrdGe b g) : OrdGe (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
  have hdeg : pq.1.degree + pq.2.degree = m.degree := by
    rw [← hpq']
    first
      | exact (map_add Finsupp.degree pq.1 pq.2).symm
      | exact (Finsupp.degree_add pq.1 pq.2).symm
  by_cases h1 : pq.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
end Formalism.L2.Pj.Crude
