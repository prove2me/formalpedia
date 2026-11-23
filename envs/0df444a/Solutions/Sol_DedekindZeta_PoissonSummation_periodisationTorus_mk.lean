-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.periodisationTorus_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:50.971462+00:00
-- url     : https://prove2.me/submissions/9eb306cb-e7c6-4813-b9ad-0e6f9069f757

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
theorem _root_.solution (x : V) :
    periodisationTorus L f (QuotientAddGroup.mk x) = periodisation L f x := rfl
end DedekindZeta.PoissonSummation
