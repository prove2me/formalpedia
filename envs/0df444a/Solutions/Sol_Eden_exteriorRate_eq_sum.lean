-- Prove2me | solution 1 for Eden.exteriorRate_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:47.93584+00:00
-- url     : https://prove2.me/submissions/a840488e-ce29-421d-8736-5aedcf97dac9

import Definitions.Def_Eden_ExteriorLimits
import Definitions.Def_Eden_SelectedSums
import Definitions.Def_Eden_KaplanYorke
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_Eden_ExteriorMaximalGrowth

set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (c : ℝ) (p : PhaseSpace) (s : ExteriorIndex k) :
    exteriorRate k c p s = ∑ j ∈ s.val, factorExponents c p j := by
  unfold exteriorRate
  change (∑ i : Fin k, factorExponents c p (s.val.orderEmbOfFin s.property i)) = _
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
  rw [Finset.sum_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]
end Eden
