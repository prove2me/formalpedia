-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.continuous_torusEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:45.230399+00:00
-- url     : https://prove2.me/submissions/23bc57e0-164b-4c3f-bcd6-cfd083d47a8b

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
variable {d : ℕ} (b : Basis (Fin d) ℤ L)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution : Continuous (torusEquiv L b).symm :=
  map_continuous (torusEquiv L b).symm
end DedekindZeta.PoissonSummation
