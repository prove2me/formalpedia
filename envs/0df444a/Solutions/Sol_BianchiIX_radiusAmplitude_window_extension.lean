-- Prove2me | solution 1 for BianchiIX.radiusAmplitude_window_extension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:48.807438+00:00
-- url     : https://prove2.me/submissions/20ffadd8-96ec-4c5c-80c7-b70f82ad7cf0

import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_cone
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_deriv_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_middle
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pair_bound
import Theorems.Thm_BianchiIX_amplitudeCurveExtension_pos
import Theorems.Thm_BianchiIX_contDiff_amplitudeCurveExtension
import Theorems.Thm_BianchiIX_intervalRadiusInverse_control
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.radiusAmplitude_data {k U : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hpos : ∀ x ∈ Icc a b, 0 < U x)
    (hcone : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|) :
    let J := Icc (k b) (k a)
    let u := radiusAmplitude k U a b
    let du := radiusAmplitudeSlope k U a b
    (∀ x ∈ Icc a b, u (k x) = U x) ∧ (∀ x ∈ J, 0 < u x) ∧
      (∀ x ∈ J, HasDerivWithinAt u (du x) J x) ∧ ContinuousOn du J ∧
      ∀ x ∈ J, |du x| ≤ Real.sqrt (u x) := by
  intro J u du
  obtain ⟨_, _, hleft, hmaps, _, hder⟩ := intervalRadiusInverse_control hab hk hd
  let g := intervalRadiusInverse k a b
  have hgc : ContinuousOn g J := fun x hx => (hder x hx).continuousWithinAt
  have hdk : ContinuousOn (deriv k) (Icc a b) := fun x hx =>
    ((hk x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  have hdU : ContinuousOn (deriv U) (Icc a b) := fun x hx =>
    ((hU x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  refine ⟨?_, (fun x hx => hpos (g x) (hmaps hx)), ?_, ?_, ?_⟩
  · intro x hx
    exact congrArg U (hleft hx)
  · intro x hx
    simpa only [u, du, J, g, radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using!
      (((hU (g x) (hmaps hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x (hder x hx))
  · exact (hdU.comp hgc hmaps).div (hdk.comp hgc hmaps) (fun x hx => (hd (g x) (hmaps hx)).ne)
  · intro x hx
    change |deriv U (g x) / deriv k (g x)| ≤ Real.sqrt (U (g x))
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (hd (g x) (hmaps hx)).ne)).mpr (hcone (g x) (hmaps hx))

end
end


/-- A closed output window inherits continuous endpoint slopes and the original cone constant. -/
theorem solution {k U W : ℝ → ℝ} {a b l r θ B : ℝ}
    (hab : a < b) (hlr : l < r) (hwindow : Icc l r ⊆ Icc (k b) (k a)) (hθ : θ ≤ 1)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ θ * (Real.sqrt (U x) * |deriv k x|))
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ θ * (Real.sqrt (W x) * |deriv k x|))
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeWindowExtension k U a b l r
    let w := radiusAmplitudeWindowExtension k W a b l r
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, k x ∈ Icc l r →
        u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ θ * Real.sqrt (u x) ∧ |deriv w x| ≤ θ * Real.sqrt (w x) := by
  intro u w
  obtain ⟨_, _, hleft, hmaps, _, _⟩ := intervalRadiusInverse_control hab hk hd
  have Hdata (V : ℝ → ℝ) (hV : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 V x)
      (hpos : ∀ x ∈ Icc a b, 0 < V x)
      (hc : ∀ x ∈ Icc a b, |deriv V x| ≤ θ * (Real.sqrt (V x) * |deriv k x|)) :
      (∀ x ∈ Icc l r, 0 < radiusAmplitude k V a b x) ∧
      (∀ x ∈ Icc l r, HasDerivWithinAt (radiusAmplitude k V a b)
        (radiusAmplitudeSlope k V a b x) (Icc l r) x) ∧
      ContinuousOn (radiusAmplitudeSlope k V a b) (Icc l r) ∧
      ∀ x ∈ Icc l r, |radiusAmplitudeSlope k V a b x| ≤ θ * Real.sqrt (radiusAmplitude k V a b x) := by
    have hc1 (x : ℝ) (hx : x ∈ Icc a b) := (hc x hx).trans
      (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hθ)
    obtain ⟨_, hp, hv, hdc, _⟩ := radiusAmplitude_data hab hk hd hV hpos hc1
    refine ⟨fun x hx => hp x (hwindow hx), fun x hx => (hv x (hwindow hx)).mono hwindow,
      hdc.mono hwindow, ?_⟩
    intro x hx
    let z := intervalRadiusInverse k a b x
    have hz : z ∈ Icc a b := hmaps (hwindow hx)
    change |deriv V z / deriv k z| ≤ θ * Real.sqrt (V z)
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr (hd z hz).ne)).mpr
    exact (hc z hz).trans_eq (by ring)
  obtain ⟨hpu, hdu, hcu, hconeU'⟩ := Hdata U hU hposU hconeU
  obtain ⟨hpw, hdw, hcw, hconeW'⟩ := Hdata W hW hposW hconeW
  refine ⟨contDiff_amplitudeCurveExtension hlr hpu hdu hcu,
    contDiff_amplitudeCurveExtension hlr hpw hdw hcw, ?_, ?_⟩
  · intro x hx hxJ
    have hmatch (V : ℝ → ℝ) (hpos : ∀ x ∈ Icc l r, 0 < radiusAmplitude k V a b x) :
        radiusAmplitudeWindowExtension k V a b l r (k x) = V x := by
      rw [radiusAmplitudeWindowExtension, amplitudeCurveExtension_middle hxJ (hpos _ hxJ).le,
        radiusAmplitude, hleft hx]
    refine ⟨hmatch U hpu, hmatch W hpw, ?_, ?_⟩
    · rw [show u = amplitudeCurveExtension l r (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b) by rfl,
        amplitudeCurveExtension_deriv_middle hlr hpu hdu hxJ, radiusAmplitudeSlope, hleft hx]
    · rw [show w = amplitudeCurveExtension l r (radiusAmplitude k W a b) (radiusAmplitudeSlope k W a b) by rfl,
        amplitudeCurveExtension_deriv_middle hlr hpw hdw hxJ, radiusAmplitudeSlope, hleft hx]
  · intro x
    exact ⟨amplitudeCurveExtension_pos hlr.le hpu hconeU' hθ x,
      amplitudeCurveExtension_pos hlr.le hpw hconeW' hθ x,
      amplitudeCurveExtension_pair_bound hlr.le hpu hpw hconeU' hconeW' hθ
        (fun y hy => hB _ (hmaps (hwindow hy))) x,
      amplitudeCurveExtension_cone hlr hpu hdu hconeU' hθ x,
      amplitudeCurveExtension_cone hlr hpw hdw hconeW' hθ x⟩
