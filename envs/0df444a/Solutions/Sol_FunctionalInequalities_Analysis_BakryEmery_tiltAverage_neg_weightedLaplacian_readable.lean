-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:26.019768+00:00
-- url     : https://prove2.me/submissions/3341459b-7554-4541-9de1-1c4f19d4270f

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_expTilt_tilted_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gradient_sub_inner_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integrable_gradient_expTilt_readable
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_weightedLaplacian_eq_zero_of_notMem_tsupport_readable

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
omit [MeasurableSpace E] [BorelSpace E] in
/-- Tilting the potential by a linear function adds a drift: `ℒ_{V - ⟪z,·⟫} f = ℒ_V f + ⟪z, ∇f⟫`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_sub_inner {V f : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
    weightedLaplacian (fun y => V y - ⟪z, y⟫) f x = weightedLaplacian V f x + ⟪z, gradient f x⟫ := by
    rw [weightedLaplacian_apply, weightedLaplacian_apply]
    rw [gradient_sub_inner_readable z x hV]
    rw [inner_sub_left]
    ring
/-- The generator integrates to zero: `∫ ℒ_W f dμ_W = 0` for `μ_W = m.tilted (-W)`, `W ∈ C¹` and a
compactly supported `C²` function `f`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero {W f : E → ℝ} (hW : ContDiff ℝ 1 W)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian W f x ∂(m.tilted (-W)) = 0 := by
    have h :=
      integral_inner_gradient_tilted m hW hf hfc
        (g := fun _ : E => (1 : ℝ)) contDiff_const
    simp at h
    have h' : -(∫ x, weightedLaplacian W f x ∂(m.tilted (-W))) = 0 := by
      simpa only [integral_neg] using h.symm
    exact neg_eq_zero.mp h'
omit [m.IsAddHaarMeasure] in
/-- For a `C¹` potential and a compactly supported `C²` function, `ℒ_V f` is integrable for every
exponential tilt of `m.tilted (-W)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_expTilt {V W f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    Integrable (fun x => weightedLaplacian V f x) (expTilt (m.tilted (-W)) z) := by
  have hc : Continuous (fun x => weightedLaplacian V f x) := continuous_weightedLaplacian hV hf
  have hcs : HasCompactSupport (fun x => weightedLaplacian V f x) := by
    refine hfc.mono' ?_
    intro x hx
    by_contra hnot
    exact hx (weightedLaplacian_eq_zero_of_notMem_tsupport_readable V hnot)
  unfold expTilt
  exact hc.integrable_of_hasCompactSupport hcs
/-- **BKL (48)** for compactly supported `C²` functions: with `μ = m.tilted (-V)`, `V ∈ C¹`,
`F_{-ℒu}(z) = ⟪z, F_{∇u}(z)⟫` for every `z ∈ E`, where `ℒu = Δu - ⟪∇V, ∇u⟫`. -/
theorem solution {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    FunctionalInequalities.Analysis.BakryEmery.tiltAverage (m.tilted (-V)) (fun x => -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x) z =
      ⟪z, FunctionalInequalities.Analysis.BakryEmery.tiltAverage (m.tilted (-V)) (gradient f) z⟫ := by
    unfold FunctionalInequalities.Analysis.BakryEmery.tiltAverage
    by_cases h : Integrable (fun x => Real.exp ((-V) x)) m
    · let W : E → ℝ := fun y => V y - ⟪z, y⟫
      have hlin : ContDiff ℝ 1 (fun y : E => ⟪z, y⟫) :=
        (innerSL ℝ z).contDiff
      have hW : ContDiff ℝ 1 W := by
        simpa only [W] using hV.sub hlin
      have hz :
          FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z = m.tilted (-W) := by
        simpa only [W] using FunctionalInequalities.Analysis.BakryEmery.expTilt_tilted_readable m h z
      have hgrad :
          Integrable (gradient f) (FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) :=
        FunctionalInequalities.Analysis.BakryEmery.integrable_gradient_expTilt_readable (m := m) hf hfc z
      have hinner :
          Integrable (fun x => ⟪z, gradient f x⟫)
            (FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) :=
        (innerSL ℝ z).integrable_comp hgrad
      have hL :
          Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x)
            (FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) :=
        FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_expTilt (m := m) hV hf hfc z
      have hzero :
          (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W f x
            ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) = 0 := by
        calc
          (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W f x
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) =
              ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W f x ∂(m.tilted (-W)) := by
                rw [hz]
          _ = 0 := FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero m hW hf hfc
      have hpoint (x : E) :
          FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W f x =
            FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x + ⟪z, gradient f x⟫ := by
        change FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian
            (fun y => V y - ⟪z, y⟫) f x =
          FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x + ⟪z, gradient f x⟫
        exact FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian_sub_inner z x
          (hV.differentiable (by norm_num) x)
      have hadd :
          (∫ x, (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x + ⟪z, gradient f x⟫)
            ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) = 0 := by
        have heq :
            (∫ x, (FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x + ⟪z, gradient f x⟫)
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) =
              ∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian W f x
                ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun x => (hpoint x).symm)
        exact heq.trans hzero
      have hsum :
          (∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) +
            ∫ x, ⟪z, gradient f x⟫
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) = 0 := by
        rw [← integral_add hL hinner]
        exact hadd
      have hneg :
          -(∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) =
            ∫ x, ⟪z, gradient f x⟫
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) := by
        linarith
      calc
        (∫ x, -FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x
            ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) =
            -(∫ x, FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian V f x
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)) := by
                rw [integral_neg]
        _ = ∫ x, ⟪z, gradient f x⟫
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z) := hneg
        _ = ⟪z, ∫ x, gradient f x
              ∂(FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z)⟫ :=
          integral_inner hgrad z
    · have hzero : m.tilted (-V) = 0 :=
        tilted_of_not_integrable h
      have hz : FunctionalInequalities.Analysis.BakryEmery.expTilt (m.tilted (-V)) z = 0 := by
        unfold FunctionalInequalities.Analysis.BakryEmery.expTilt
        rw [hzero]
        exact tilted_zero_measure _
      rw [hz]
      simp
