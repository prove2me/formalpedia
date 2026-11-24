-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_prod_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:37.839261+00:00
-- url     : https://prove2.me/submissions/36d1f284-0468-4e8e-8e1a-798ecbd347e7

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
theorem _root_.solution {ι σ : Type} (s : Finset ι) (f : ι → σ →₀ ℕ) :
    ∏ i ∈ s, (monomial (f i) (1 : k) : MvPowerSeries σ k) = monomial (∑ i ∈ s, f i) 1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · first
      | simp
      | simp [MvPowerSeries.monomial_zero_eq_C]
      | (rw [Finset.prod_empty, Finset.sum_empty]; rfl)
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, MvPowerSeries.monomial_mul_monomial, one_mul]
end Formalism.L2.Pj.Crude
