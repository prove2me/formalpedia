-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_exact_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:51:23.600107+00:00
-- url     : https://prove2.me/submissions/8161760f-11df-46ff-acec-2d8faf93e11c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫ ω, (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      (h : ℝ) * X.σ ^ 2 := by
  classical
  let Y : Ω → ℝ := fun ω => X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let Z : ℝ → Ω → ℝ := fun ξ ω =>
    (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) - (h : ℝ) * X.ψ ξ) - 1) / ξ
  let D : ℝ → Ω → ℝ := fun θ ω => Z θ ω - Y ω
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  let B : ℝ := ∫ ω, (Y ω) ^ 2 ∂P
  let E : ℝ → ℝ := fun θ => ∫ ω, (D θ ω) ^ 2 ∂P
  change B = a
  have hYm : MemLp Y 2 P := by
    simpa only [Y] using avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two X hν τ hτ T hbounded h
  have hZm (θ : ℝ) (hθ : 0 ≤ θ) : MemLp (Z θ) 2 P := by
    simpa only [Z] using (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered X hν τ hτ T hbounded h θ hθ).1
  have hDm (θ : ℝ) (hθ : 0 ≤ θ) : MemLp (D θ) 2 P :=
    (hZm θ hθ).sub hYm
  have hErr : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [E, D, Y, Z] using avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_real_L2_convergence X hν τ hτ T hbounded h
  have hZsq (θ : ℝ) (hθ : 0 ≤ θ) : (∫ ω, (Z θ ω) ^ 2 ∂P) = (Real.exp (a * θ ^ 2) - 1) / θ ^ 2 := by
    simpa only [Z, a, pow_two, mul_assoc] using (avram_wave5_03a_actual_source_rightCont_stopped_gaussian_cross_quotient X hν τ hτ T hbounded h θ θ hθ hθ)
  have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq : Tendsto (fun θ : ℝ => θ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hid.pow 2
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact pow_pos (show (0 : ℝ) < θ from hθ) 2
  have hsec : Tendsto (fun ε : ℝ => (Real.exp (a * ε) - 1) / ε)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa only [zero_mul, add_zero] using
      (avram_wave5_03a_exp_quadratic_secant_right_limit a 0)
  have hZlim : Tendsto (fun θ : ℝ => ∫ ω, (Z θ ω) ^ 2 ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    have heq : (fun θ : ℝ => ∫ ω, (Z θ ω) ^ 2 ∂P) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun θ : ℝ => (Real.exp (a * θ ^ 2) - 1) / θ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact hZsq θ (le_of_lt (show (0 : ℝ) < θ from hθ))
    have ht := hsec.comp hsq
    change Tendsto (fun θ : ℝ => (Real.exp (a * θ ^ 2) - 1) / θ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 a) at ht
    exact ht.congr' heq.symm
  have hYint : Integrable (fun ω => (Y ω) ^ 2) P := (memLp_two_iff_integrable_sq hYm.aestronglyMeasurable).mp hYm
  have hCrossBound (θ : ℝ) (hθ : 0 ≤ θ) :
      |∫ ω, Y ω * D θ ω ∂P| ≤ Real.sqrt B * Real.sqrt (E θ) := by
    have hDa : MemLp (fun ω => |D θ ω|) 2 P := by
      have ht := (hDm θ hθ).abs
      change MemLp (fun ω => |D θ ω|) 2 P at ht
      exact ht
    have hYa : MemLp (fun ω => |Y ω|) 2 P := by
      have ht := hYm.abs
      change MemLp (fun ω => |Y ω|) 2 P at ht
      exact ht
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (Y ω)))
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (D θ ω)))
      (by simpa using hYa) (by simpa using hDa)
    have hh' : (∫ ω, |Y ω| * |D θ ω| ∂P) ≤
        Real.sqrt B * Real.sqrt (E θ) := by
      simpa only [B, E, Real.sqrt_eq_rpow, Real.rpow_two, sq_abs] using hh
    have hi := norm_integral_le_integral_norm (fun ω => Y ω * D θ ω) (μ := P)
    change |∫ ω, Y ω * D θ ω ∂P| ≤
      (∫ ω, |Y ω * D θ ω| ∂P) at hi
    exact le_trans (by simpa only [abs_mul] using hi) hh'
  have hSqrtErr : Tendsto (fun θ => Real.sqrt (E θ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hErr
    change Tendsto (fun θ => Real.sqrt (E θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt (0 : ℝ))) at ht
    simpa only [Real.sqrt_zero] using ht
  have hRoot : Tendsto (fun θ => Real.sqrt B * Real.sqrt (E θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hSqrtErr
  have hCrossZero : Tendsto (fun θ => ∫ ω, Y ω * D θ ω ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hl : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ),
        -(Real.sqrt B * Real.sqrt (E θ)) ≤ ∫ ω, Y ω * D θ ω ∂P := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact (abs_le.mp (hCrossBound θ (le_of_lt (show (0 : ℝ) < θ from hθ)))).1
    have hu : ∀ᶠ θ : ℝ in 𝓝[>] (0 : ℝ),
        (∫ ω, Y ω * D θ ω ∂P) ≤ Real.sqrt B * Real.sqrt (E θ) := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact (abs_le.mp (hCrossBound θ (le_of_lt (show (0 : ℝ) < θ from hθ)))).2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using hRoot.neg) hRoot hl hu
  have hExpand (θ : ℝ) (hθ : 0 ≤ θ) :
      (∫ ω, (Z θ ω) ^ 2 ∂P) =
        B + 2 * (∫ ω, Y ω * D θ ω ∂P) + E θ := by
    have hDi : Integrable (fun ω => (D θ ω) ^ 2) P :=
      (memLp_two_iff_integrable_sq (hDm θ hθ).aestronglyMeasurable).mp (hDm θ hθ)
    have hCi : Integrable (fun ω => Y ω * D θ ω) P :=
      hYm.integrable_mul (hDm θ hθ)
    calc
      (∫ ω, (Z θ ω) ^ 2 ∂P) =
          (∫ ω, (Y ω) ^ 2 + 2 * (Y ω * D θ ω) + (D θ ω) ^ 2 ∂P) := by
        congr 1
        funext ω
        dsimp [D]
        ring
      _ = B + 2 * (∫ ω, Y ω * D θ ω ∂P) + E θ := by
        calc
          _ = (∫ ω, (Y ω) ^ 2 + 2 * (Y ω * D θ ω) ∂P) +
                (∫ ω, (D θ ω) ^ 2 ∂P) :=
            integral_add (hYint.add (hCi.const_mul 2)) hDi
          _ = _ := by
            calc
              _ = ((∫ ω, (Y ω) ^ 2 ∂P) + (∫ ω, 2 * (Y ω * D θ ω) ∂P)) + (∫ ω, (D θ ω) ^ 2 ∂P) := by
                congr 1
                exact integral_add hYint (hCi.const_mul 2)
              _ = _ := by simp only [integral_const_mul, B, E]
  have hExpandLim : Tendsto (fun θ : ℝ => ∫ ω, (Z θ ω) ^ 2 ∂P)
      (𝓝[>] (0 : ℝ)) (𝓝 B) := by
    have hB : Tendsto (fun _ : ℝ => B) (𝓝[>] (0 : ℝ)) (𝓝 B) := tendsto_const_nhds
    have hTwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) := tendsto_const_nhds
    have ht := (hB.add (hTwo.mul hCrossZero)).add hErr
    have heq : (fun θ : ℝ => ∫ ω, (Z θ ω) ^ 2 ∂P) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun θ => B + 2 * (∫ ω, Y ω * D θ ω ∂P) + E θ) := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact hExpand θ (le_of_lt (show (0 : ℝ) < θ from hθ))
    have hfinal := ht.congr' heq.symm
    simpa only [mul_zero, add_zero] using hfinal
  exact tendsto_nhds_unique hExpandLim hZlim
