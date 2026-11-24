-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_gaussianPerimeter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T12:54:50.856353+00:00
-- url     : https://prove2.me/submissions/9ca23047-7e16-4ce7-aa8c-2207294b599c

module
public import Definitions.Def_GaussianPerimeter_Averaging
public import Definitions.Def_GaussianPerimeter_HausdorffNormalization
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Definitions.Def_GaussianPerimeter_RadialIntegration
public import Definitions.Def_GaussianPerimeter_SphereCap
public import Definitions.Def_GaussianPerimeter_Construction
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_append_measurable
public import Theorems.Thm_GaussianPerimeter_VolumeComparison_fix_measurable
public import Theorems.Thm_GaussianPerimeter_capRho_pos
public import Theorems.Thm_GaussianPerimeter_capScale_pos
public import Theorems.Thm_GaussianPerimeter_capTail_le_one
public import Theorems.Thm_GaussianPerimeter_capTail_nonneg
public import Theorems.Thm_GaussianPerimeter_lintegral_gaussian_radial
public import Theorems.Thm_GaussianPerimeter_lowerBound_of_nazarov
public import Theorems.Thm_GaussianPerimeter_one_sub_capTail_le_uniformSphere
public import Theorems.Thm_GaussianPerimeter_radialDensity_measurable
public import Theorems.Thm_GaussianPerimeter_shiftedCapTail_measurable
public import Theorems.Thm_GaussianPerimeter_tendsto_capScale_zero
public import Theorems.Thm_GaussianPerimeter_volume_le_normalized_hausdorff
public import Theorems.Thm_P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6
public import Theorems.Thm_P2M_GaussianPerimeter_mul_lintegral_acceptance_le___90af1dc06317
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.append_measurable
attribute [local fun_prop] GaussianPerimeter.VolumeComparison.fix_measurable
attribute [local fun_prop] P2M_GaussianPerimeter_VolumeComparison_append_measurable__f5f150faf8d6


section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace
namespace GaussianPerimeter
private theorem gaussian_density_split (n : ℕ) (ρ r : ℝ) :
    (2 * Real.pi) ^ (-(n + 1 : ℝ) / 2) * Real.exp (-(ρ ^ 2 + r ^ 2) / 2) =
      (Real.exp (-ρ ^ 2 / 2) / Real.sqrt (2 * Real.pi)) *
        ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-r ^ 2 / 2)) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [show -(n + 1 : ℝ) / 2 = -(n : ℝ) / 2 + -(1 / 2) by ring,
    Real.rpow_add hπ, Real.rpow_neg hπ.le, ← Real.sqrt_eq_rpow,
    show -(ρ ^ 2 + r ^ 2) / 2 = -ρ ^ 2 / 2 + -r ^ 2 / 2 by ring, Real.exp_add]
  ring
private theorem acceptance_ge_capTail (n : ℕ) (hn : 2 ≤ n) (ρ r : ℝ)
    (hρ : 0 < ρ) (hr : 0 < r) :
    ENNReal.ofReal (1 - capTail n (ρ / Real.sqrt (ρ ^ 2 + r ^ 2))) ≤
      facetAcceptanceProbability n ρ r := by
  let u := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  let t := ρ / Real.sqrt (ρ ^ 2 + r ^ 2)
  have hDen : 0 < Real.sqrt (ρ ^ 2 + r ^ 2) := by positivity
  have hR : ρ < Real.sqrt (ρ ^ 2 + r ^ 2) := by
    apply (Real.lt_sqrt hρ.le).2
    linarith [sq_pos_of_pos hr]
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨(div_pos hρ hDen).le, ((div_lt_one hDen).2 hR).le⟩
  have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).norm_eq_one 0
  change ENNReal.ofReal (1 - capTail n t) ≤ _
  rw [ENNReal.ofReal_sub _ (capTail_nonneg ht), ENNReal.ofReal_one]
  exact one_sub_capTail_le_uniformSphere n hn hu hρ hR
private theorem eventually_one_le_floor {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n in atTop, 1 ≤ ⌊b / capScale a n⌋₊ := by
  filter_upwards [eventually_gt_atTop (0 : ℕ), (tendsto_capScale_zero ha).eventually_lt_const hb]
    with n hn hs
  apply Nat.le_floor
  simpa using (le_div_iff₀ (capScale_pos ha hn)).2 (by simpa using hs.le)
private theorem lowerBound_gaussianPolytope {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / capScale a n⌋₊ : ℝ) *
        (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (shiftedRadialDensity n w * (1 - shiftedCapTail a n w) ^ (⌊b / capScale a n⌋₊ - 1)))
        ≤ Γ (n + 1) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_one_le_floor ha hb]
    with n hn htrials
  let N := ⌊b / capScale a n⌋₊ - 1
  let ρ := capRho a n
  let m := Real.sqrt ((n : ℝ) - 1)
  let d := Real.exp (-ρ ^ 2 / 2) / Real.sqrt (2 * Real.pi)
  let p (r : ℝ) := shiftedCapTail a n (r - m)
  let f : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun r => (1 - p r) ^ N)
  have hρ : 0 < ρ := capRho_pos ha (by omega)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hpMeas : Measurable p :=
    (shiftedCapTail_measurable a n).comp
      (show Measurable (fun r : ℝ => r - m) by fun_prop)
  have hf : Measurable f :=
    Measurable.indicator ((measurable_const.sub hpMeas).pow_const N) measurableSet_Ioi
  have hp (r : ℝ) : p r = capTail n (ρ / Real.sqrt (ρ ^ 2 + r ^ 2)) := by
    have h : m + (r - m) = r := by ring
    unfold p shiftedCapTail
    rw [if_pos hn]
    change capTail n (ρ / Real.sqrt ((m + (r - m)) ^ 2 + ρ ^ 2)) = _
    rw [h, add_comm]
  have hAcc (r : ℝ) : ENNReal.ofReal (f r) ≤ facetAcceptanceProbability n ρ r ^ N := by
    by_cases hr : 0 < r
    · have hden : 0 < Real.sqrt (ρ ^ 2 + r ^ 2) := by positivity
      have ht : 0 ≤ ρ / Real.sqrt (ρ ^ 2 + r ^ 2) := by positivity
      have ht₁ : ρ / Real.sqrt (ρ ^ 2 + r ^ 2) ≤ 1 := (div_le_one hden).2 <| by
        apply (Real.le_sqrt (by positivity) (by positivity)).2
        nlinarith
      have hnon : 0 ≤ 1 - p r := by rw [hp]; exact sub_nonneg.mpr (capTail_le_one hn ⟨ht, ht₁⟩)
      unfold f
      rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr), ENNReal.ofReal_pow hnon, hp]
      exact pow_le_pow_left' (acceptance_ge_capTail n hn ρ r hρ hr) N
    · simp [f, hr]
  have hnorm :
      (∫⁻ y : EuclideanSpace ℝ (Fin n), ENNReal.ofReal
        ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2) * f ‖y‖)) =
        ∫⁻ r : ℝ, ENNReal.ofReal (radialDensity n r * f r) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact lintegral_gaussian_radial k hf
  have hdom : (volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) / (2 : ℝ≥0∞) ^ n) •
        μH[(n : ℝ)] := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact volume_le_normalized_hausdorff k
  have hGeo := mul_lintegral_acceptance_le_Γ n N ρ hdom
  have hGe : ENNReal.ofReal d *
      (∫⁻ r : ℝ, ENNReal.ofReal (radialDensity n r * f r)) ≤
      ∫⁻ y : EuclideanSpace ℝ (Fin n), facetAcceptanceProbability n ρ ‖y‖ ^ N *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(n + 1 : ℝ) / 2) *
          Real.exp (-(ρ ^ 2 + ‖y‖ ^ 2) / 2)) := by
    rw [← hnorm, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_mono fun y => ?_
    rw [gaussian_density_split, ENNReal.ofReal_mul hd, ENNReal.ofReal_mul (by positivity :
      0 ≤ (2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2))]
    simpa only [mul_left_comm, mul_comm, mul_assoc] using
      mul_le_mul_right (hAcc ‖y‖) (ENNReal.ofReal d *
        ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖y‖ ^ 2 / 2)))
  have hShift :
      (∫⁻ w in Ioc (-W) W, ENNReal.ofReal
        (shiftedRadialDensity n w * (1 - shiftedCapTail a n w) ^ N)) ≤
        ∫⁻ r : ℝ, ENNReal.ofReal (radialDensity n r * f r) := by
    have hf' : Measurable (fun r : ℝ => ENNReal.ofReal (radialDensity n r * f r)) :=
      ENNReal.continuous_ofReal.measurable.comp ((radialDensity_measurable n).mul hf)
    rw [← (measurePreserving_add_left (volume : Measure ℝ) m).lintegral_comp hf']
    refine (le_of_eq ?_).trans
      (lintegral_mono' (Measure.restrict_le_self (s := Ioc (-W) W)) le_rfl)
    apply lintegral_congr
    intro w
    change ENNReal.ofReal (radialDensity n (m + w) * (1 - shiftedCapTail a n w) ^ N) =
      ENNReal.ofReal (radialDensity n (m + w) * f (m + w))
    by_cases hw : m + w ∈ Ioi (0 : ℝ)
    · have hm : m + w - m = w := by ring
      simp only [f, indicator_of_mem hw, p, hm]
    · have hz : radialDensity n (m + w) = 0 := by
        rw [radialDensity, radialKernel, indicator_of_notMem hw, zero_div]
      simp [hz]
  have hN : N + 1 = ⌊b / capScale a n⌋₊ := Nat.sub_add_cancel htrials
  rw [hN] at hGeo
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc, ENNReal.ofReal_natCast]
  exact (mul_le_mul_right ((mul_le_mul_right hShift _).trans hGe) _).trans hGeo
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop :=
  lowerBound_of_nazarov ha hb hW (lowerBound_gaussianPolytope ha hb)
end GaussianPerimeter
