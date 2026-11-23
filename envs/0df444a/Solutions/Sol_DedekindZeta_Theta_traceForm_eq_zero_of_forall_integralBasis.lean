-- Prove2me | solution 1 for DedekindZeta.Theta.traceForm_eq_zero_of_forall_integralBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:12:18.316309+00:00
-- url     : https://prove2.me/submissions/ed723f35-8548-4281-953a-9574fbd620c3

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_traceFormLin_mixedEmbedding

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (ζ : mixedSpace K)
    (hz : ∀ i, traceForm K ζ (integralBasis K i) = 0) : ζ = 0 := by
  have hlin : traceFormLin K ζ = 0 := by
    refine (latticeBasis K).ext (fun i => ?_)
    rw [latticeBasis_apply, traceFormLin_mixedEmbedding]
    simpa using hz i
  have hval : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) = 0 := by
    have hv := LinearMap.congr_fun hlin
      (⟨ζ.1, fun w => starRingEnd ℂ (ζ.2 w)⟩ : mixedSpace K)
    rw [LinearMap.zero_apply, traceFormLin_apply] at hv
    rw [← hv]
    have hre : ∀ w : {w : InfinitePlace K // w.IsComplex},
        Complex.normSq (ζ.2 w) = (ζ.2 w * starRingEnd ℂ (ζ.2 w)).re := by
      intro w; rw [Complex.mul_conj, Complex.ofReal_re]
    simp_rw [hre]
  have hA : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w :=
    Finset.sum_nonneg (fun w _ => mul_self_nonneg _)
  have hB : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hA0 : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) = 0 := by linarith
  have hB0 : (∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w)) = 0 := by
    linarith
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg (ζ.1 w))).mp hA0 w
      (Finset.mem_univ w)
    exact mul_self_eq_zero.mp this
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex}, ζ.2 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => Complex.normSq_nonneg (ζ.2 w))).mp hB0 w (Finset.mem_univ w)
    exact Complex.normSq_eq_zero.mp this
  ext w
  · exact hreal w
  · rw [Prod.snd_zero, Pi.zero_apply]; rw [hcplx w]
end DedekindZeta.Theta
