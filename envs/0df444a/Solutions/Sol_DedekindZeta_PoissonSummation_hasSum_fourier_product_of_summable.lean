-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.hasSum_fourier_product_of_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:08:50.311113+00:00
-- url     : https://prove2.me/submissions/4431fc31-7a44-4d30-91a3-29cf738f1292

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_fourierCoeffProd_eq_mFourierCoeff

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
theorem _root_.solution
    {F : (Fin d → AddCircle (1 : ℝ)) → ℂ} (hF : Continuous F)
    (h : Summable (fun n : Fin d → ℤ => fourierCoeffProd F n))
    (θ : Fin d → AddCircle (1 : ℝ)) :
    HasSum (fun n : Fin d → ℤ => (∏ i, fourier (n i) (θ i)) • fourierCoeffProd F n)
      (F θ) := by
  -- Bundle `F` as a continuous map and transfer the coefficient identity.
  set f : C(UnitAddTorus (Fin d), ℂ) := ⟨F, hF⟩ with hf
  have hcoeff : mFourierCoeff (⇑f) = fun n => fourierCoeffProd F n := by
    funext n; rw [fourierCoeffProd_eq_mFourierCoeff, hf, ContinuousMap.coe_mk]
  have hsum : Summable (mFourierCoeff (⇑f)) := by rw [hcoeff]; exact h
  have hHS := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := f) hsum θ
  -- Rewrite `mFourierCoeff f i • mFourier i θ` into the target form.
  have hfun : (fun i : Fin d → ℤ => mFourierCoeff (⇑f) i • (mFourier i) θ)
      = fun n : Fin d → ℤ => (∏ i, fourier (n i) (θ i)) • fourierCoeffProd F n := by
    funext n
    have hc : mFourierCoeff (⇑f) n = fourierCoeffProd F n := by
      rw [fourierCoeffProd_eq_mFourierCoeff, hf, ContinuousMap.coe_mk]
    rw [mFourier]
    simp only [ContinuousMap.coe_mk, hc, smul_eq_mul, mul_comm]
  rw [hfun] at hHS
  exact hHS
end DedekindZeta.PoissonSummation
