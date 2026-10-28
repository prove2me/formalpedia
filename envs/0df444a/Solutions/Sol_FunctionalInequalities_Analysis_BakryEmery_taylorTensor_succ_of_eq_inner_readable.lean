-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.taylorTensor_succ_of_eq_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:12.161472+00:00
-- url     : https://prove2.me/submissions/7cd18f21-3f89-4d97-9b7b-d2900ffa1b9f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_SquareIntegrable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_perm_of_contDiff_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_self_apply_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_perm_inner_init_last_readable

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff ENNReal
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Lp
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Lemma 3.6 from the tilt identity: if `F_g(w) = ⟪w, F_G(w)⟫` for every `w` with `F_G` smooth,
then `T_{d+1} g = S_{d+1} T_d G`. This is the tensor part of the proof of
`taylorTensor_neg_weightedLaplacian`, isolated from the smooth compactly supported setting. -/
theorem solution (μ : Measure E) {g : E → ℝ} {G : E → E}
    (hG : ContDiff ℝ ∞ (FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G))
    (hEq : FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ g = fun w => ⟪w, FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G w⟫) (d : ℕ) :
    FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ g (d + 1) = FunctionalInequalities.Analysis.Tensor.symmetrizeML (FunctionalInequalities.Analysis.Tensor.appendInner (FunctionalInequalities.Analysis.BakryEmery.taylorTensor μ G d)) := by
  set Φ := FunctionalInequalities.Analysis.BakryEmery.tiltAverage μ G with hΦ
  ext h
  simp only [FunctionalInequalities.Analysis.BakryEmery.taylorTensor, FunctionalInequalities.Analysis.Tensor.symmetrizeML, FunctionalInequalities.Analysis.Tensor.appendInner,
    smul_apply,
    sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rw [hEq, ← hΦ]
  rw [FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_readable hG d 0 h]
  simp only [inner_zero_left, zero_add, Function.comp_apply]
  change
    ((d + 1).factorial : ℝ)⁻¹ •
        ∑ k : Fin (d + 1), ⟪h k, (iteratedFDeriv ℝ d Φ 0) (k.removeNth h)⟫ =
      ((d + 1).factorial : ℝ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin (d + 1)),
          ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
            h (σ (Fin.last d))⟫
  have hs : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪(iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫) =
      (d.factorial : ℝ) *
        ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    apply FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_readable
    intro τ v
    exact FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_readable hG d 0 v τ
  have hsum : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
          h (σ (Fin.last d))⟫) =
      ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    simp_rw [smul_apply, real_inner_smul_left]
    rw [← Finset.mul_sum, hs]
    field_simp [Nat.factorial_ne_zero]
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => real_inner_comm _ _
