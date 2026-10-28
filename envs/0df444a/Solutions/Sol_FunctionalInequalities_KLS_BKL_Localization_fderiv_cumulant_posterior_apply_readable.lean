-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.fderiv_cumulant_posterior_apply_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:32:32.318757+00:00
-- url     : https://prove2.me/submissions/8a76c514-cba8-4fae-9dd2-5e61f461fadc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CumulantDerivative
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_contDiff_logPartition_joint_readable
import Theorems.Thm_FunctionalInequalities_Probability_Posterior_cumulant_compactPosterior_readable

section
noncomputable section
open scoped ContDiff
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem FunctionalInequalities.Analysis.directional_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) :
    ContDiff ℝ ∞ (directional hs f) := by
  induction hs with
  | nil => exact hf
  | cons h hs IH =>
    exact (ContinuousLinearMap.apply ℝ F h).contDiff.comp (IH.fderiv_right (by simp))
private theorem FunctionalInequalities.Analysis.directional_two {f : E → F} (hf : ContDiff ℝ ∞ f) (v w x : E) :
    directional [v, w] f x = fderiv ℝ (fderiv ℝ f) x v w := by
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  have hDf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hDf.differentiable (by simp) x) (differentiableAt_const w)]
  simp
/-- Adjacent directional derivatives commute by genuine real C² symmetry. -/
theorem FunctionalInequalities.Analysis.directional_swap {f : E → F} (hf : ContDiff ℝ ∞ f) (hs : List E) (v w : E) :
    directional (v :: w :: hs) f = directional (w :: v :: hs) f := by
  funext x
  have hg := directional_contDiff hf hs
  have he (u t : E) : directional (u :: t :: hs) f x = directional [u,t] (directional hs f) x := rfl
  rw [he, he, directional_two hg, directional_two hg]
  exact hg.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top) v w
/-- Full permutation symmetry follows from adjacent swaps; no tensor symmetry is a premise. -/
theorem FunctionalInequalities.Analysis.directional_perm {f : E → F} (hf : ContDiff ℝ ∞ f) {hs ks : List E}
    (h : hs.Perm ks) : directional hs f = directional ks f := by
  induction h with
  | nil => rfl
  | cons v h IH =>
    change (fun x => fderiv ℝ (directional _ f) x v) = (fun x => fderiv ℝ (directional _ f) x v)
    rw [IH]
  | swap v w hs => exact directional_swap hf hs w v
  | trans h1 h2 IH1 IH2 => exact IH1.trans IH2
/-- The directional list convention is exactly the raw iterated Fréchet derivative. -/
theorem FunctionalInequalities.Analysis.directional_ofFn {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) f x = iteratedFDeriv ℝ m f x h := by
  induction m generalizing x with
  | zero => simp [directional]
  | succ m IH =>
    rw [List.ofFn_succ]
    change fderiv ℝ (directional (List.ofFn (Fin.tail h)) f) x (h 0) = _
    have he : directional (List.ofFn (Fin.tail h)) f =
        fun y => iteratedFDeriv ℝ m f y (Fin.tail h) := funext (fun y => IH (Fin.tail h) y)
    rw [he]
    exact ((hf.differentiable_iteratedFDeriv (m := m)
      (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m)) x).iteratedFDeriv_succ_apply_left').symm
/-- Raw real C∞ iterated derivatives are symmetric under every slot permutation. -/
theorem FunctionalInequalities.Analysis.iteratedFDeriv_perm {f : E → F} (hf : ContDiff ℝ ∞ f) (m : ℕ)
    (h : Fin m → E) (σ : Equiv.Perm (Fin m)) (x : E) :
    iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h := by
  rw [← directional_ofFn hf, ← directional_ofFn hf]
  exact congrFun (directional_perm hf (σ.ofFn_comp_perm h)) x
end
end
end

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
private theorem FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_cons_eq_snoc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {m : ℕ}
    (hf : ContDiff ℝ ∞ f) (h : Fin m → E) (v : E) :
    iteratedFDeriv ℝ (m + 1) f x (Fin.cons v h) =
      iteratedFDeriv ℝ (m + 1) f x (Fin.snoc h v) := by
  have hperm :
      (Fin.snoc h v) ∘ ⇑(FunctionalInequalities.KLS.BKL.Localization.snocToCons m) = Fin.cons v h := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [FunctionalInequalities.KLS.BKL.Localization.snocToCons]
    · simp [FunctionalInequalities.KLS.BKL.Localization.snocToCons]
  have hp :=
    FunctionalInequalities.Analysis.iteratedFDeriv_perm
      hf (m + 1) (Fin.snoc h v) (FunctionalInequalities.KLS.BKL.Localization.snocToCons m) x
  rw [hperm] at hp
  exact hp
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- **The `c`-derivative of a cumulant is the next cumulant**: `D_c κ_m(h)[v] = κ_{m+1}(h, v)` (BKL p. 20,
`∇ᵐv_t(0) = κ_{m+1}`; the noise of (67) only moves `c`). -/
theorem solution {m : ℕ} (hm : 1 ≤ m) (h : Fin m → EuclideanSpace ℝ (Fin n))
    (p : FunctionalInequalities.KLS.BKL.Localization.Param n) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
        FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) m h) p (v, 0) =
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v) := by
  let ψ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q => FunctionalInequalities.Probability.Posterior.logPartition μ q.1 q.2
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
  have hdiff :
      Differentiable ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => iteratedFDeriv ℝ m ψ q) :=
    hψ.differentiable_iteratedFDeriv
      (m := m) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))
  let w : FunctionalInequalities.KLS.BKL.Localization.Param n := (v, 0)
  let Ulast : Fin (m + 1) → FunctionalInequalities.KLS.BKL.Localization.Param n := Fin.snoc U w
  have hderiv :
      fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
        iteratedFDeriv ℝ (m + 1) ψ p Ulast := by
    calc
      fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => (iteratedFDeriv ℝ m ψ q) U) p (v, 0) =
          (fderiv ℝ (fun q : FunctionalInequalities.KLS.BKL.Localization.Param n => iteratedFDeriv ℝ m ψ q) p (v, 0)) U :=
        fderiv_continuousMultilinear_apply_const_apply
          hdiff.differentiableAt U (v, 0)
      _ = iteratedFDeriv ℝ (m + 1) ψ p (Fin.cons w U) := by
        simpa [w] using
          (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := ψ) (x := p)
            (Fin.cons w U)).symm
      _ = iteratedFDeriv ℝ (m + 1) ψ p Ulast :=
        FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_cons_eq_snoc hψ U w
  rw [hderiv]
  let hv : Fin (m + 1) → EuclideanSpace ℝ (Fin n) := Fin.snoc h v
  have hU : (fun i : Fin (m + 1) => ((hv i, 0) : FunctionalInequalities.KLS.BKL.Localization.Param n)) = Ulast := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [hv, Ulast, w]
    · simp [hv, Ulast, U]
  have hs := FunctionalInequalities.KLS.BKL.Localization.iteratedFDeriv_param_slice ψ hψ hv p.1 p.2
  rw [hU] at hs
  calc
    iteratedFDeriv ℝ (m + 1) ψ p Ulast =
        iteratedFDeriv ℝ (m + 1)
          (fun y => FunctionalInequalities.Probability.Posterior.logPartition μ y p.2) p.1 (Fin.snoc h v) := by
      simpa [ψ, hv] using hs.symm
    _ = FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc p.1 p.2 :
        Measure (EuclideanSpace ℝ (Fin n))) (m + 1) (Fin.snoc h v) := by
      have hcumulant :=
        FunctionalInequalities.Probability.Posterior.cumulant_compactPosterior_readable μ hc p.1 p.2
          (hm := Nat.succ_le_succ (Nat.zero_le m))
      exact (congrArg (fun T => T (Fin.snoc h v)) hcumulant).symm
