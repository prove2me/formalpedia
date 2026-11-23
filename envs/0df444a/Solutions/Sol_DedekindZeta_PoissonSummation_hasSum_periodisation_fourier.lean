-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.hasSum_periodisation_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:51.679873+00:00
-- url     : https://prove2.me/submissions/cfb963e1-1138-4c86-aa77-48ee5ea750a2

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_summable_periodisation_fourier
import Theorems.Thm_DedekindZeta_PoissonSummation_periodisation_eq_tsum_fourier

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1176
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1182
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (x : V) :
    HasSum (fun w : dualLattice L =>
      𝐞 (⟪x, (w : V)⟫) •
        ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)))
      (periodisation L f x) := by
  rw [periodisation_eq_tsum_fourier L f x]
  exact (summable_periodisation_fourier L f x).hasSum
end DedekindZeta.PoissonSummation
