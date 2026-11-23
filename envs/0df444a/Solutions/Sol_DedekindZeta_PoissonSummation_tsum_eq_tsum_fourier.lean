-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.tsum_eq_tsum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:28:43.778849+00:00
-- url     : https://prove2.me/submissions/29a6ebf9-4d2f-4f5d-ba6c-8baad2574b0d

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_periodisation_zero
import Theorems.Thm_DedekindZeta_PoissonSummation_hasSum_periodisation_fourier

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
theorem _root_.solution :
    ∑' v : L, (f : V → ℂ) v
      = (ZLattice.covolume L : ℂ)⁻¹ * ∑' w : dualLattice L, 𝓕 (f : V → ℂ) w := by
  -- Evaluate the torus Fourier inversion at `x = 0`: the characters become `1`.
  have h := hasSum_periodisation_fourier L f 0
  simp only [inner_zero_left, AddChar.map_zero_eq_one, one_smul] at h
  rw [← periodisation_zero L f, ← h.tsum_eq, tsum_mul_left]
end DedekindZeta.PoissonSummation
