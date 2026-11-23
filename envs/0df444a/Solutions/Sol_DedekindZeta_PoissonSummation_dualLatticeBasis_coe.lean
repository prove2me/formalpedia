-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.dualLatticeBasis_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:05:10.375301+00:00
-- url     : https://prove2.me/submissions/deb208e1-b9e1-4c42-ac98-761e96ed2cd5

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
theorem _root_.solution (i : Fin d) :
    ((dualLatticeBasis L b i : dualLattice L) : V) = dualBasisR L b i := by
  rw [dualLatticeBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
end DedekindZeta.PoissonSummation
