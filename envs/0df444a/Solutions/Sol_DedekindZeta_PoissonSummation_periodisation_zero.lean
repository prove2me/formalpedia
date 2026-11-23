-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.periodisation_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:20.720859+00:00
-- url     : https://prove2.me/submissions/e6989df3-906f-43fe-aa4d-fd372ed321d6

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution : periodisation L f 0 = ∑' v : L, (f : V → ℂ) v := by
  simp only [periodisation_apply, zero_add]
end DedekindZeta.PoissonSummation
