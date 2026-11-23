-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.fourierCoeffProd_eq_mFourierCoeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:04.26586+00:00
-- url     : https://prove2.me/submissions/32e2ad79-beb0-4806-9ade-f24e710ff1bb

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_828
variable {d : ℕ}
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (F : (Fin d → AddCircle (1 : ℝ)) → ℂ)
    (n : Fin d → ℤ) : fourierCoeffProd F n = mFourierCoeff F n := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  -- `mFourier (-n) θ = ∏ i, fourier (-(n i)) (θ i) = ∏ i, conj (fourier (n i) (θ i))`.
  rw [mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply, fourier_neg]
end DedekindZeta.PoissonSummation
