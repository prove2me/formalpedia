-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_contDiff_compact_bounded_weak_deriv_approximation_of_support_subset_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:15:36.295734+00:00
-- url     : https://prove2.me/submissions/972112f8-cf1a-4378-8b3f-4bb9cfff04b9

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_convolution_eq_of_hasWeakDerivAlong_408915f

section
noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Mollification
end FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Mollification
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- `L²` contraction of the mollifier in `eLpNorm` form. -/
theorem FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_convolution_sq_le_408915f φ hf) (by norm_num)
/-- The mollification of a locally integrable function is continuous. -/
theorem FunctionalInequalities.Analysis.Mollification.continuous_convolution {f : V → E} (hf : LocallyIntegrable f m) :
    Continuous (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) :=
  HasCompactSupport.continuous_convolution_left _ (φ.hasCompactSupport_normed (μ := m))
    φ.continuous_normed hf
/-- The mollification of an `L²` function is again `L²`. -/
theorem FunctionalInequalities.Analysis.Mollification.memLp_convolution {f : V → E} (hf : MemLp f 2 m) :
    MemLp (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m :=
  ⟨(continuous_convolution φ (hf.locallyIntegrable one_le_two)).aestronglyMeasurable,
    (eLpNorm_convolution_le φ hf.1).trans_lt hf.2⟩
end Contraction
section Convergence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
/-- The support of a mollification with `rOut ≤ ε` lies in the closed `ε`-thickening of the
support of the function. -/
theorem FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening_of_rOut_le (φ : ContDiffBump (0 : V)) {ε : ℝ}
    (hφ : φ.rOut ≤ ε) (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening ε (tsupport f) := by
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  rw [φ.support_normed_eq] at ha
  refine mem_cthickening_of_dist_le (a + b) b ε _ (subset_tsupport _ hb) ?_
  rw [dist_eq_norm, add_sub_cancel_right]
  rw [mem_ball, dist_zero_right] at ha
  exact ha.le.trans hφ
end Convergence
end
end
end
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section BoundedWeakDerivativeApproximation
open MeasureTheory Filter Set Metric
open scoped ContDiff Convolution Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
/-- The existing normalized-bump estimate supplies one common uniform bound. -/
private theorem FunctionalInequalities.Analysis.norm_normed_convolution_le_three_mul {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x‖ ≤ 3 * C := by
  have hxy (y : EuclideanSpace ℝ (Fin n)) : dist (η y) (η x) ≤ 2 * C := by
    calc
      dist (η y) (η x) = ‖η y - η x‖ := dist_eq_norm _ _
      _ ≤ ‖η y‖ + ‖η x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hbound y) (hbound x)
      _ = 2 * C := by ring
  have hd := φ.dist_normed_convolution_le hη.aestronglyMeasurable (fun y _ => hxy y)
  calc
    _ ≤ ‖(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) x - η x‖ + ‖η x‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ 2 * C + C := add_le_add (by simpa only [dist_eq_norm] using hd) (hbound x)
    _ = 3 * C := by ring
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
set_option maxHeartbeats 1200000 in
/-- Support- and radius-controlled form of the bounded all-coordinate approximation: when the supports of `η`
and of every `a i` lie in a compact `K`, then for every `ε > 0` the smooth approximants, their coordinate
derivatives and the original data all live in ONE compact `S ⊆ cthickening ε K` (bump radii at most `ε`), with
the uniform bound `3 * C`, global L2 coordinate derivatives converging in L2, and full-sequence almost-everywhere
convergence. Every finite dimension, zero included. Support for Letwin arXiv:2607.24164v1 (2.6). -/
theorem solution {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    {a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hηK : Function.support η ⊆ K) (haK : ∀ i : Fin n, Function.support (a i) ⊆ K)
    {ε : ℝ} (hε : 0 < ε)
    (hweak : ∀ i : Fin n, FunctionalInequalities.Analysis.HasWeakDerivAlong η (a i)
      (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧ S ⊆ cthickening ε K ∧
      Function.support η ⊆ S ∧ (∀ i : Fin n, Function.support (a i) ⊆ S) ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m : ℕ, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧ (∀ x, ‖θ m x‖ ≤ 3 * C) ∧
          ∀ i : Fin n,
            Function.support (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ S ∧
            MemLp (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
              (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        (∀ i : Fin n,
          Tendsto (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
            2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
  have hηc : HasCompactSupport η := HasCompactSupport.of_support_subset_isCompact hK hηK
  have hac (i : Fin n) : HasCompactSupport (a i) := HasCompactSupport.of_support_subset_isCompact hK (haK i)
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (ε / ((m : ℝ) + 1)) / 2
      rOut := ε / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hm : 0 < ε / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => ε / ((m : ℝ) + 1)) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, mul_zero, one_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
  have hφle (m : ℕ) : (φ m).rOut ≤ ε := by
    dsimp [φ]
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hm' : 0 < (m : ℝ) + 1 := by linarith
    apply (div_le_iff₀ hm').2
    nlinarith [hε]
  have hφratio : ∀ᶠ m : ℕ in (atTop : Filter ℕ), (φ m).rOut ≤ 2 * (φ m).rIn :=
    Filter.Eventually.of_forall (fun m : ℕ => by
      change (ε / ((m : ℝ) + 1)) ≤
        2 * ((ε / ((m : ℝ) + 1)) / 2)
      have h :
          (2 : ℝ) * ((ε / ((m : ℝ) + 1)) / 2) =
            ε / ((m : ℝ) + 1) := by
        ring
      rw [h])
  let Kη : Set (EuclideanSpace ℝ (Fin n)) := cthickening ε (tsupport η)
  let Ki : Fin n → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => cthickening ε (tsupport (a i))
  have hKη : IsCompact Kη := by
    dsimp [Kη]
    exact hηc.isCompact.cthickening
  have hKi : ∀ i : Fin n, IsCompact (Ki i) := by
    intro i
    dsimp [Ki]
    exact (hac i).isCompact.cthickening
  let S : Set (EuclideanSpace ℝ (Fin n)) := Kη ∪ ⋃ i, Ki i
  have hS : IsCompact S := by
    dsimp [S]
    exact hKη.union (isCompact_iUnion hKi)
  let θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η
  let dvm : Fin n → ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun i m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (a i)
  have hθsmooth (m : ℕ) : ContDiff ℝ ∞ (θ m) := by
    dsimp [θ]
    exact
      ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).contDiff_normed (n := (⊤ : ℕ∞))) hη
  have hθcompact (m : ℕ) : HasCompactSupport (θ m) := by
    dsimp [θ]
    exact
      HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).hasCompactSupport_normed (μ := volume)) hηc
  have hθsupport (m : ℕ) : Function.support (θ m) ⊆ Kη := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) ⊆ Kη
    simpa [Kη] using
      (FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening_of_rOut_le (φ m) (hφle m) η)
  have hdisupport (i : Fin n) (m : ℕ) :
      Function.support (dvm i m) ⊆ Ki i := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (a i)) ⊆ Ki i
    simpa [Ki] using
      (FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening_of_rOut_le (φ m) (hφle m) (a i))
  have hderiv (i : Fin n) (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) = dvm i m x := by
    simpa [θ, dvm] using
      FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_408915f (hweak i) (φ m) x
  have hdactual (i : Fin n) (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)) ⊆ Ki i := by
    intro x hx
    have hx' : x ∈ Function.support (dvm i m) := by
      change dvm i m x ≠ 0
      rw [← hderiv i m x]
      exact hx
    exact hdisupport i m hx'
  have hdmem (i : Fin n) (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h :
        MemLp (dvm i m) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      FunctionalInequalities.Analysis.Mollification.memLp_convolution (φ m) (ha2 i)
    rw [show (fun x => fderiv ℝ (θ m) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)) = dvm i m by
      funext x
      exact hderiv i m x]
    exact h
  have hdlim (i : Fin n) :
      Tendsto (fun m => eLpNorm (dvm i m - a i) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    simpa [dvm] using
      (FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_408915f (φ := φ) hφlim (ha2 i))
  have hdlim' (i : Fin n) :
      Tendsto
        (fun m => eLpNorm
          (fun x => fderiv ℝ (θ m) x
              (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    have heq :
        (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x
                (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x)
            2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (fun m => eLpNorm (dvm i m - a i) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      change
        fderiv ℝ (θ m) x (EuclideanSpace.basisFun (Fin n) ℝ i) - a i x =
          dvm i m x - a i x
      rw [hderiv i m x]
    rw [heq]
    exact hdlim i
  have hηsupport : Function.support η ⊆ Kη := by
    exact (subset_tsupport η).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hasupport (i : Fin n) : Function.support (a i) ⊆ Ki i := by
    exact (subset_tsupport (a i)).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hθbound (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      ‖θ m x‖ ≤ 3 * C := by
    simpa [θ] using
      (norm_normed_convolution_le_three_mul hη hbound (φ m) x)
  have hae :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun m => θ m x) atTop (𝓝 (η x)) := by
    simpa [θ] using
      (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
        (φ := φ) hφlim hφratio hη)
  have hηKs : tsupport η ⊆ K := closure_minimal hηK hK.isClosed
  have haKs (i : Fin n) : tsupport (a i) ⊆ K := closure_minimal (haK i) hK.isClosed
  have hSK : S ⊆ cthickening ε K := by
    intro x hx
    rcases hx with hx | hx
    · exact (Metric.cthickening_subset_of_subset ε hηKs) hx
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact (Metric.cthickening_subset_of_subset ε (haKs i)) hi
  refine ⟨S, hS, hSK, ?_, ?_, ?_⟩
  · exact hηsupport.trans (by
      intro x hx
      exact Or.inl hx)
  · intro i
    exact (hasupport i).trans (by
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩))
  · refine ⟨θ, ?_, ?_, hae⟩
    · intro m
      refine ⟨hθsmooth m, hθcompact m, ?_, hθbound m, ?_⟩
      · exact hθsupport m |>.trans (by
          intro x hx
          exact Or.inl hx)
      · intro i
        exact ⟨
          (hdactual i m).trans (by
            intro x hx
            exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)),
          hdmem i m⟩
    · intro i
      exact hdlim' i
