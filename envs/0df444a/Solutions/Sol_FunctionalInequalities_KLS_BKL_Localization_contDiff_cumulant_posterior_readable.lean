-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulant_posterior_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:07.303009+00:00
-- url     : https://prove2.me/submissions/54c7fea1-e2fd-4316-bbc4-26746165d720

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_cumulant_compactPosterior_readable

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
private theorem FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_param_slice
    {n : ℕ} (ψ : Param n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (c : EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ m (fun y : EuclideanSpace ℝ (Fin n) => ψ (y, Q)) c h =
      iteratedFDeriv ℝ m ψ (c, Q)
        (fun i => (h i, (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let K := E →L[ℝ] E
  let L : E →L[ℝ] E × K := ContinuousLinearMap.inl ℝ E K
  let a : E × K := (0, Q)
  let g : E × K → ℝ := fun z => ψ (z + a)
  have hg : ContDiff ℝ ∞ g := by
    exact hψ.comp
      (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ (fun _ : E × K => a)))
  have hm_top : (m : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr le_top
  have hcomp :=
    L.iteratedFDeriv_comp_right hg c (i := m) hm_top
  have hshift :
      iteratedFDeriv ℝ m g (L c) =
        iteratedFDeriv ℝ m ψ (L c + a) := by
    simpa [g] using
      (iteratedFDeriv_comp_add_right (𝕜 := ℝ) m a (L c))
  have hcomp' := congrArg (fun T => T h) hcomp
  rw [hshift] at hcomp'
  simpa [E, K, L, a, g, Function.comp_def,
    ContinuousLinearMap.inl_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using hcomp'
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- **Joint smoothness of the posterior cumulants** in the parameter `p = (c, Q)`: for a compactly supported
prior and `m ≥ 1`, `p ↦ κ_m(μ_p)(h)` is `C^∞` on the whole parameter space (BKL arXiv:2610.05474v1, Section 4:
`κ_m = D_c^m ψ` with `ψ` jointly smooth). -/
theorem solution {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) := by
  let ψ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun p => FunctionalInequalities.Probability.Posterior.logPartition μ p.1 p.2
  let U : Fin m → FunctionalInequalities.KLS.BKL.Localization.Param n := fun i => (h i, 0)
  have hψ : ContDiff ℝ ∞ ψ := by
    simpa [ψ] using FunctionalInequalities.Probability.Posterior.contDiff_logPartition_joint_readable μ hc
  have hcum :
      (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
        FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n))) m h) =
        (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) := by
    funext q
    calc
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n))) m h =
          iteratedFDeriv ℝ m (fun y =>
            FunctionalInequalities.Probability.Posterior.logPartition μ y q.2) q.1 h :=
        congrArg (fun T => T h) (FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_readable μ hc q.1 q.2 hm)
      _ = (iteratedFDeriv ℝ m ψ q) U := by
        simpa [ψ, U] using
          FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_param_slice ψ hψ h q.1 q.2
  rw [hcum]
  have htop : (∞ : ℕ∞ω) + (m : ℕ∞ω) ≤ ∞ := by
    rw [← WithTop.coe_natCast m, ← WithTop.coe_add]
    exact WithTop.coe_le_coe.mpr le_top
  have hΦ :
      ContDiff ℝ ∞ (fun p : FunctionalInequalities.KLS.BKL.Localization.Param n => iteratedFDeriv ℝ m ψ p) :=
    hψ.iteratedFDeriv_right (m := ∞) (i := m) htop
  let A :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => FunctionalInequalities.KLS.BKL.Localization.Param n) ℝ U
  simpa [A, Function.comp_def] using A.contDiff.comp hΦ
