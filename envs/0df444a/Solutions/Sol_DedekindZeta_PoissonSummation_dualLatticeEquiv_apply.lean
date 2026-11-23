-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.dualLatticeEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:58.739812+00:00
-- url     : https://prove2.me/submissions/e601120d-5412-4a70-ae9a-c88a2abc4d0e

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
theorem _root_.solution (w : dualLattice L) (i : Fin d) :
    dualLatticeEquiv L b w i = (dualLatticeBasis L b).repr w i := rfl
end DedekindZeta.PoissonSummation
