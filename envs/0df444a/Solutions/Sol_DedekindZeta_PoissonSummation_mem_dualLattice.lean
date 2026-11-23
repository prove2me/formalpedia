-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.mem_dualLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:57:50.088303+00:00
-- url     : https://prove2.me/submissions/fa0d81bb-0452-427f-8dd6-e31c78308fb4

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace DedekindZeta.PoissonSummation
theorem _root_.solution {L : Submodule ℤ V} {w : V} :
    w ∈ dualLattice L ↔ ∀ v ∈ L, (⟪w, v⟫ : ℝ) ∈ (1 : Submodule ℤ ℝ) :=
  Iff.rfl
end DedekindZeta.PoissonSummation
