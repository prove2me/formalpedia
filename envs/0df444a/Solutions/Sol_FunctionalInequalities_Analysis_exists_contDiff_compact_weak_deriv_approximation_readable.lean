-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_contDiff_compact_weak_deriv_approximation_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:51.995276+00:00
-- url     : https://prove2.me/submissions/84725338-7557-46fb-89b8-2d00bd6071e4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Approximation
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_lintegral_enorm_convolution_sq_le_readable
import Theorems.Thm_FunctionalInequalities_Analysis_Mollification_tendsto_eLpNorm_convolution_sub_readable
import Theorems.Thm_FunctionalInequalities_Analysis_fderiv_convolution_eq_of_hasWeakDerivAlong_readable

section
noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace
section
open FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
section Contraction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (φ : ContDiffBump (0 : V))
/-- `L²` contraction of the mollifier in `eLpNorm` form. -/
theorem FunctionalInequalities.Analysis.Mollification.eLpNorm_convolution_le {f : V → E} (hf : AEStronglyMeasurable f m) :
    eLpNorm (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) 2 m ≤ eLpNorm f 2 m := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_convolution_sq_le_readable φ hf) (by norm_num)
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
omit [CompleteSpace E] in
/-- The support of a mollification with `rOut ≤ 1` lies in the closed `1`-thickening of the
support of the function. -/
theorem FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ : ContDiffBump (0 : V)) (hφ : φ.rOut ≤ 1)
    (f : V → E) :
    Function.support (φ.normed m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] f) ⊆
      cthickening 1 (tsupport f) :=
  support_convolution_subset_cthickening_of_rOut_le φ hφ f
end Convergence
end
end
end

noncomputable section
open MeasureTheory
open scoped ContDiff
section CompactWeakDerivativeTesting
noncomputable section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
set_option maxHeartbeats 800000 in
/-- A compact rough test with two compact L2 weak derivatives admits smooth tests
with common compact support and simultaneous L2 convergence of those derivatives.
Supporting density component for Letwin2607.24164v1 (2.6). -/
theorem solution {n : ℕ}
    {η a b : EuclideanSpace ℝ (Fin n) → ℝ} {v w : EuclideanSpace ℝ (Fin n)}
    (hηv : FunctionalInequalities.Analysis.HasWeakDerivAlong η a v) (hηw : FunctionalInequalities.Analysis.HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S ∧
      Function.support (η) ⊆ S ∧ Function.support (a) ⊆ S ∧
      Function.support (b) ⊆ S ∧
      ∃ θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ m, ContDiff ℝ ∞ (θ m) ∧ HasCompactSupport (θ m) ∧
          Function.support (θ m) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (v)) ⊆ S ∧
          Function.support (fun x => fderiv ℝ (θ m) x (w)) ⊆ S ∧
          MemLp (fun x => fderiv ℝ (θ m) x (v)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
          MemLp (fun x => fderiv ℝ (θ m) x (w)) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (v) - (a) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) ∧
        Tendsto (fun m => eLpNorm (fun x => fderiv ℝ (θ m) x (w) - (b) x)
          2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun m =>
    { rIn := (1 / ((m : ℝ) + 1)) / 2
      rOut := 1 / ((m : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
        linarith }
  have hφlim : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0) := by
    change Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφle (m : ℕ) : (φ m).rOut ≤ 1 := by
    dsimp [φ]
    have hm : 0 ≤ (m : ℝ) := by positivity
    have hm' : 0 < (m : ℝ) + 1 := by linarith
    apply (div_le_iff₀ hm').2
    nlinarith
  let Kη : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport η)
  let Ka : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport a)
  let Kb : Set (EuclideanSpace ℝ (Fin n)) := cthickening 1 (tsupport b)
  have hKη : IsCompact Kη := by
    dsimp [Kη]
    exact hηc.isCompact.cthickening
  have hKa : IsCompact Ka := by
    dsimp [Ka]
    exact hac.isCompact.cthickening
  have hKb : IsCompact Kb := by
    dsimp [Kb]
    exact hbc.isCompact.cthickening
  let θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η
  let dvm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a
  let dwm : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun m =>
    (φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b
  have hθsmooth (m : ℕ) : ContDiff ℝ ∞ (θ m) := by
    dsimp [θ]
    exact
      ((φ m).hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ m).contDiff_normed (n := (⊤ : ℕ∞))) hηv.1
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
      (FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ m) (hφle m) η)
  have hdvsupport (m : ℕ) : Function.support (dvm m) ⊆ Ka := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) ⊆ Ka
    simpa [Ka] using
      (FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ m) (hφle m) a)
  have hdwsupport (m : ℕ) : Function.support (dwm m) ⊆ Kb := by
    change
      Function.support
          ((φ m).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] b) ⊆ Kb
    simpa [Kb] using
      (FunctionalInequalities.Analysis.Mollification.support_convolution_subset_cthickening (φ m) (hφle m) b)
  have hderivv (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (θ m) x v = dvm m x := by
    simpa [θ, dvm] using FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_readable hηv (φ m) x
  have hderivw (m : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (θ m) x w = dwm m x := by
    simpa [θ, dwm] using FunctionalInequalities.Analysis.fderiv_convolution_eq_of_hasWeakDerivAlong_readable hηw (φ m) x
  have hdvactual (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x v) ⊆ Ka := by
    intro x hx
    have hx' : x ∈ Function.support (dvm m) := by
      change dvm m x ≠ 0
      rw [← hderivv m x]
      exact hx
    exact hdvsupport m hx'
  have hdwactual (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x w) ⊆ Kb := by
    intro x hx
    have hx' : x ∈ Function.support (dwm m) := by
      change dwm m x ≠ 0
      rw [← hderivw m x]
      exact hx
    exact hdwsupport m hx'
  have hdvmem (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x v) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h :
        MemLp (dvm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      FunctionalInequalities.Analysis.Mollification.memLp_convolution (φ m) ha2
    rw [show (fun x => fderiv ℝ (θ m) x v) = dvm m by
      funext x
      exact hderivv m x]
    exact h
  have hdwmem (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x w) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have h :
        MemLp (dwm m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      FunctionalInequalities.Analysis.Mollification.memLp_convolution (φ m) hb2
    rw [show (fun x => fderiv ℝ (θ m) x w) = dwm m by
      funext x
      exact hderivw m x]
    exact h
  have hdvlim :
      Tendsto (fun m => eLpNorm (dvm m - a) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_readable hφlim ha2
  have hdwlim :
      Tendsto (fun m => eLpNorm (dwm m - b) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) :=
    FunctionalInequalities.Analysis.Mollification.tendsto_eLpNorm_convolution_sub_readable hφlim hb2
  have hdvlim' :
      Tendsto
        (fun m => eLpNorm
          (fun x => fderiv ℝ (θ m) x v - a x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    have heq :
        (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x v - a x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (fun m => eLpNorm (dvm m - a) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      simp only [Pi.sub_apply]
      rw [hderivv m x]
    rw [heq]
    exact hdvlim
  have hdwlim' :
      Tendsto
        (fun m => eLpNorm
          (fun x => fderiv ℝ (θ m) x w - b x) 2
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0) := by
    have heq :
        (fun m => eLpNorm
            (fun x => fderiv ℝ (θ m) x w - b x) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          (fun m => eLpNorm (dwm m - b) 2
            (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
      funext m
      congr 2
      funext x
      simp only [Pi.sub_apply]
      rw [hderivw m x]
    rw [heq]
    exact hdwlim
  have hηsupport : Function.support η ⊆ Kη := by
    exact (subset_tsupport η).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hasupport : Function.support a ⊆ Ka := by
    exact (subset_tsupport a).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  have hbsupport : Function.support b ⊆ Kb := by
    exact (subset_tsupport b).trans (by
      intro x hx
      exact Metric.self_subset_cthickening _ hx)
  refine ⟨Kη ∪ (Ka ∪ Kb), hKη.union (hKa.union hKb), ?_, ?_, ?_, ?_⟩
  · exact hηsupport.trans (by
      intro x hx
      exact Or.inl hx)
  · exact hasupport.trans (by
      intro x hx
      exact Or.inr (Or.inl hx))
  · exact hbsupport.trans (by
      intro x hx
      exact Or.inr (Or.inr hx))
  · refine ⟨θ, ?_, hdvlim', hdwlim'⟩
    intro m
    exact
      ⟨hθsmooth m, hθcompact m,
        hθsupport m |>.trans (by
          intro x hx
          exact Or.inl hx),
        hdvactual m |>.trans (by
          intro x hx
          exact Or.inr (Or.inl hx)),
        hdwactual m |>.trans (by
          intro x hx
          exact Or.inr (Or.inr hx)),
        hdvmem m, hdwmem m⟩
