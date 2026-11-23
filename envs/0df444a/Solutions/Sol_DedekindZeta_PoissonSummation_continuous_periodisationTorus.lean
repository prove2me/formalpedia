-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.continuous_periodisationTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:25.671018+00:00
-- url     : https://prove2.me/submissions/680b0f92-9e81-44ff-bd70-b3f93d7bc860

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_continuous_periodisation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution : Continuous (periodisationTorus L f) :=
  -- A map out of the quotient (coinduced) topology is continuous iff its
  -- composite with the quotient map is; that composite is `periodisation L f`.
  (continuous_periodisation L f).quotient_liftOn' _
end DedekindZeta.PoissonSummation
