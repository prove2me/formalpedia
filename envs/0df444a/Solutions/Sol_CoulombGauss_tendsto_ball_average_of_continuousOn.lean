-- Prove2me | solution 1 for CoulombGauss.tendsto_ball_average_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:20:25.750191+00:00
-- url     : https://prove2.me/submissions/eb916f3e-b489-4ef4-9d39-064eda0c5f88

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

set_option autoImplicit false

open CoulombGauss MeasureTheory Filter Topology Metric in
theorem solution (U : Set Vec3) (hU : IsOpen U) (ρ : Vec3 → ℝ)
    (hρ : ContinuousOn ρ U) (c : Vec3) (hc : c ∈ U) :
    Tendsto (fun R : ℝ => (volume (ball c R)).toReal⁻¹ * ∫ x in ball c R, ρ x)
      (𝓝[>] 0) (𝓝 (ρ c)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hcont : ContinuousAt ρ c := hρ.continuousAt (hU.mem_nhds hc)
  obtain ⟨δ₂, hδ₂, hδ⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (by linarith)
  have hδpos : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hmem : Set.Ioo (0 : ℝ) (min δ₁ δ₂) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hδpos
  filter_upwards [hmem] with R hR
  obtain ⟨hR0, hRδ⟩ := hR
  have hR1 : R < δ₁ := lt_of_lt_of_le hRδ (min_le_left _ _)
  have hR2 : R < δ₂ := lt_of_lt_of_le hRδ (min_le_right _ _)
  -- the closed ball lies in U
  have hcb : closedBall c R ⊆ U := (closedBall_subset_ball hR1).trans hball
  have hint : IntegrableOn ρ (ball c R) volume :=
    ((hρ.mono hcb).integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall
  have hfin : volume (ball c R) < ⊤ := measure_ball_lt_top
  have hpos : 0 < volume (ball c R) := Metric.measure_ball_pos volume c hR0
  have hvol : 0 < (volume (ball c R)).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hconst : IntegrableOn (fun _ : Vec3 => ρ c) (ball c R) volume := integrableOn_const hfin.ne
  have hsplit : ∫ x in ball c R, (ρ x - ρ c) = (∫ x in ball c R, ρ x) - (volume (ball c R)).toReal * ρ c := by
    rw [integral_sub hint hconst, setIntegral_const, smul_eq_mul, measureReal_def]
  have hbound : ‖∫ x in ball c R, (ρ x - ρ c)‖ ≤ (ε / 2) * volume.real (ball c R) := by
    apply norm_setIntegral_le_of_norm_le_const hfin
    intro x hx
    have := hδ (lt_of_lt_of_le (mem_ball.mp hx) hR2.le)
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]
    exact this.le
  rw [measureReal_def, Real.norm_eq_abs, hsplit] at hbound
  rw [Real.dist_eq]
  set V := (volume (ball c R)).toReal with hV
  set I := ∫ x in ball c R, ρ x with hI
  have heq : V⁻¹ * I - ρ c = V⁻¹ * (I - V * ρ c) := by
    field_simp
  rw [heq, abs_mul, abs_inv, abs_of_pos hvol]
  rw [inv_mul_lt_iff₀ hvol]
  calc |I - V * ρ c| ≤ ε / 2 * V := hbound
    _ < V * ε := by nlinarith
