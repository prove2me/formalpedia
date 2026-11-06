-- Prove2me | solution 1 for BianchiIX.fderiv_moving_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:57:27.471193+00:00
-- url     : https://prove2.me/submissions/a9d03625-e095-4558-915e-61b5c7feb9bf

import Theorems.Thm_BianchiIX_hasFDerivAt_moving_intervalIntegral_of_contDiffAt
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.integral_rescale_zero_one (f : ℝ → ℝ) (b : ℝ) :
    (∫ t in 0..b, f t) = ∫ t in (0 : ℝ)..1, b * f (t * b) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1) f b).symm

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.fderiv_rescaled_integrand {F : E × ℝ → ℝ} {τ : E → ℝ} {x v : E} {s : ℝ}
    (hτ : DifferentiableAt ℝ τ x) (hF : DifferentiableAt ℝ F (x, s * τ x)) :
    fderiv ℝ (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, s) (v, 0) =
      τ x * fderiv ℝ F (x, s * τ x) (v, 0) + fderiv ℝ τ x v *
        (F (x, s * τ x) + s * τ x * fderiv ℝ F (x, s * τ x) (0, 1)) := by
  let J := fderiv ℝ F (x, s * τ x)
  let c := fderiv ℝ τ x v
  have hc := hτ.hasFDerivAt.comp (x, s) (f := Prod.fst) hasFDerivAt_fst
  have hp := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.mul hc)
  have hg := hc.mul (hF.hasFDerivAt.comp (x, s)
    (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) hp)
  change HasFDerivAt (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) _ _ at hg
  have hJ : J (v, s * c) = J (v, 0) + (s * c) * J (0, 1) := by
    have heq : (v, s * c) = (v, (0 : ℝ)) + (s * c) • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [heq, map_add, map_smul, smul_eq_mul]
  rw [hg.fderiv]
  change τ x * J (v, s * c + τ x * 0) + F (x, s * τ x) * c = _
  rw [mul_zero, add_zero, hJ]
  ring

end
end

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


/-- Leibniz's formula from local joint regularity on the actual integration segment. -/
theorem solution {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E}
    (hτ : ContDiffAt ℝ 1 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 1 F (x, t)) (v : E) :
    fderiv ℝ (fun y => ∫ t in 0..τ y, F (y, t)) x v =
      (∫ t in 0..τ x, fderiv ℝ F (x, t) (v, 0)) + F (x, τ x) * fderiv ℝ τ x v := by
  let G : E × ℝ → ℝ := fun p => τ p.1 * F (p.1, p.2 * τ p.1)
  let J : ℝ → (E × ℝ) →L[ℝ] ℝ := fun s => fderiv ℝ F (x, s * τ x)
  have htime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : s * τ x ∈ Icc 0 (τ x) :=
    ⟨mul_nonneg hs.1 hpos, by simpa using mul_le_mul_of_nonneg_right hs.2 hpos⟩
  have hFc : ContinuousOn (fun s => F (x, s * τ x)) (Icc (0 : ℝ) 1) := fun s hs =>
    ((hF _ (htime s hs)).continuousAt.comp (f := fun u : ℝ => (x, u * τ x)) (g := F) (continuousAt_const.prodMk
      (continuousAt_id.mul continuousAt_const))).continuousWithinAt
  have hJc : ContinuousOn J (Icc (0 : ℝ) 1) := fun s hs =>
    (((hF _ (htime s hs)).continuousAt_fderiv (by norm_num)).comp
      (f := fun u : ℝ => (x, u * τ x)) (g := fderiv ℝ F)
      (continuousAt_const.prodMk (continuousAt_id.mul continuousAt_const))).continuousWithinAt
  have hGc (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 1 G (x, s) := by
    have hcτ : ContDiffAt ℝ 1 (fun p : E × ℝ => τ p.1) (x, s) := hτ.comp _ contDiffAt_fst
    have hp : ContDiffAt ℝ 1 (fun p : E × ℝ => (p.1, p.2 * τ p.1)) (x, s) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.mul hcτ)
    exact hcτ.mul ((hF _ (htime s hs)).comp (x, s)
      (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) (g := F) hp)
  have hGi : IntervalIntegrable
      (fun s => (fderiv ℝ G (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
    intro s hs
    exact ((((hGc s hs).continuousAt_fderiv (by norm_num)).comp
      (continuousAt_const.prodMk continuousAt_id)).clm_comp continuousAt_const).continuousWithinAt
  have hB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun u => u * F (x, u * τ x))
        (F (x, s * τ x) + s * τ x * J s (0, 1)) s := by
    have hp : HasDerivAt (fun u : ℝ => (x, u * τ x)) (0, τ x) s := by
      simpa using (hasDerivAt_const s x).prodMk ((hasDerivAt_id s).mul_const (τ x))
    have hh := (hasDerivAt_id s).mul
      (((hF _ (htime s hs)).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hp)
    apply hh.congr_deriv
    have heq : J s (0, τ x) = τ x * J s (0, 1) := by
      rw [← smul_eq_mul, ← map_smul]
      congr 1
      simp
    change 1 * F (x, s * τ x) + s * J s (0, τ x) = _
    rw [heq]
    ring
  have hci : ContinuousOn (fun s => F (x, s * τ x) + s * τ x * J s (0, 1)) (Icc (0 : ℝ) 1) :=
    hFc.add ((continuousOn_id.mul continuousOn_const).mul (hJc.clm_apply continuousOn_const))
  have hboundary := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hB s (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hs))
    (hci.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1))
  simp only [one_mul, zero_mul, sub_zero] at hboundary
  rw [(hasFDerivAt_moving_intervalIntegral_of_contDiffAt hτ hpos hF).fderiv,
    ContinuousLinearMap.intervalIntegral_apply hGi]
  have heq : (∫ s in (0 : ℝ)..1, (fderiv ℝ G (x, s)).comp (ContinuousLinearMap.inl ℝ E ℝ) v) =
      ∫ s in (0 : ℝ)..1, τ x * J s (v, 0) + fderiv ℝ τ x v *
        (F (x, s * τ x) + s * τ x * J s (0, 1)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact fderiv_rescaled_integrand (hτ.differentiableAt (by norm_num))
      ((hF _ (htime s (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hs))).differentiableAt (by norm_num))
  have h1 : IntervalIntegrable (fun s => τ x * J s (v, 0)) volume 0 1 :=
    (continuousOn_const.mul (hJc.clm_apply continuousOn_const)).intervalIntegrable_of_Icc (by norm_num)
  have h2 : IntervalIntegrable (fun s => fderiv ℝ τ x v *
      (F (x, s * τ x) + s * τ x * J s (0, 1))) volume 0 1 :=
    (continuousOn_const.mul hci).intervalIntegrable_of_Icc (by norm_num)
  rw [heq, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul, hboundary]
  rw [integral_rescale_zero_one (fun t => fderiv ℝ F (x, t) (v, 0)) (τ x),
    intervalIntegral.integral_const_mul]
  ring
