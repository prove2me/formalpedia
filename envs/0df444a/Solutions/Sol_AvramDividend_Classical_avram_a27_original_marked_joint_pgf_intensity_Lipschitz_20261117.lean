-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_marked_joint_pgf_intensity_Lipschitz_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:37:51.643233+00:00
-- url     : https://prove2.me/submissions/75f3f7f5-e36c-43e6-948b-2cd6a55f4eef

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_real_unit_interval_power_lipschitz_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z w : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    |(∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) -
      (∫ ω, w ^ (K ω) * Real.exp (θ * J ω) ∂P)| ≤
      (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) * |z - w| := by
  let Fz : Ω → ℝ := fun ω => z ^ (K ω) * Real.exp (θ * J ω)
  let Fw : Ω → ℝ := fun ω => w ^ (K ω) * Real.exp (θ * J ω)
  let W : Ω → ℝ := fun ω => (K ω : ℝ) * Real.exp (θ * J ω)
  have hIntZ : Integrable Fz P :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK z hz hz1
  have hIntW : Integrable Fw P :=
    avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK w hw hw1
  have hCountBound :=
    avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK hCount
  have hIntWeight : Integrable W P := hCountBound.1
  have hIntDiff : Integrable (fun ω => Fz ω - Fw ω) P :=
    hIntZ.sub hIntW
  have hIntDom : Integrable (fun ω => |z - w| * W ω) P :=
    hIntWeight.const_mul _
  have hPoint (ω : Ω) :
      |Fz ω - Fw ω| ≤ |z - w| * W ω := by
    have hp :=
      avram_a27_real_unit_interval_power_lipschitz_20261117
        z w hz hz1 hw hw1 (K ω)
    have he : 0 ≤ Real.exp (θ * J ω) :=
      le_of_lt (Real.exp_pos _)
    change |z ^ (K ω) * Real.exp (θ * J ω) -
        w ^ (K ω) * Real.exp (θ * J ω)| ≤
        |z - w| * ((K ω : ℝ) * Real.exp (θ * J ω))
    calc
      |z ^ (K ω) * Real.exp (θ * J ω) -
          w ^ (K ω) * Real.exp (θ * J ω)| =
          |(z ^ (K ω) - w ^ (K ω)) * Real.exp (θ * J ω)| := by
            congr 1
            ring
      _ = |z ^ (K ω) - w ^ (K ω)| *
          Real.exp (θ * J ω) := by
            rw [abs_mul, abs_of_nonneg he]
      _ ≤ ((K ω : ℝ) * |z - w|) * Real.exp (θ * J ω) :=
        mul_le_mul_of_nonneg_right hp he
      _ = |z - w| * ((K ω : ℝ) * Real.exp (θ * J ω)) := by ring
  have hDom :
      (fun ω => |Fz ω - Fw ω|) ≤ᵐ[P]
      (fun ω => |z - w| * W ω) :=
    Filter.Eventually.of_forall hPoint
  have hIntegralDom :=
    integral_mono_ae hIntDiff.abs hIntDom hDom
  have hIntegralDiff :
      (∫ ω, Fz ω - Fw ω ∂P) =
      (∫ ω, Fz ω ∂P) - (∫ ω, Fw ω ∂P) :=
    integral_sub hIntZ hIntW
  change |(∫ ω, Fz ω ∂P) - (∫ ω, Fw ω ∂P)| ≤
      (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) * |z - w|
  calc
    |(∫ ω, Fz ω ∂P) - (∫ ω, Fw ω ∂P)| =
        |∫ ω, Fz ω - Fw ω ∂P| := by rw [hIntegralDiff]
    _ ≤ (∫ ω, |Fz ω - Fw ω| ∂P) :=
      abs_integral_le_integral_abs
    _ ≤ (∫ ω, |z - w| * W ω ∂P) := hIntegralDom
    _ = |z - w| * (∫ ω, W ω ∂P) := by rw [integral_const_mul]
    _ ≤ |z - w| *
          (((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :=
      mul_le_mul_of_nonneg_left hCountBound.2.2 (abs_nonneg _)
    _ = _ := by ring
