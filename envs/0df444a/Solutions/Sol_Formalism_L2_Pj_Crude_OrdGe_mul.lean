-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.OrdGe.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:23.903398+00:00
-- url     : https://prove2.me/submissions/77a26880-d4c5-4e54-8098-9388217925ec

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
namespace OrdGe
theorem _root_.solution {a b : ℕ} {f g : PS k n d} (hf : OrdGe a f) (hg : OrdGe b g) : OrdGe (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  replace hp : p.1 + p.2 = m := by
    first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact Finset.mem_antidiagonal.mp hp
      | simpa using hp
  have hdeg : p.1.degree + p.2.degree = m.degree := by
    rw [← hp]
    first
      | exact (map_add _ _ _).symm
      | (simp only [Finsupp.degree_eq_weight_one, map_add])
      | (rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, ← Finset.sum_add_distrib]; rfl)
      | (simp only [Finsupp.degree_eq_sum, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib])
      | (unfold Finsupp.degree
         exact (Finsupp.sum_add_index' (h := fun _ (x : ℕ) => x) (fun _ => rfl) (fun _ _ _ => rfl)).symm)
  by_cases h1 : p.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]
end OrdGe
end Formalism.L2.Pj.Crude
