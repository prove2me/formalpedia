-- Prove2me | solution 1 for Cohen2019.Tight.prob_Y_mem_A
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:36:20.818192+00:00
-- url     : https://prove2.me/submissions/3b4a43fe-35ea-4e7d-927d-8147bd1e2058

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem pxa_law {d : ℕ} (x δ : Space d) (σ : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0) (S : Set ℝ)
    (hS : MeasurableSet S) :
    gaussNoise x σ ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S)
      = gaussianReal 0 1 S := by
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  set u : Space d := ‖δ‖⁻¹ • δ with hu
  have hun : ‖u‖ = 1 := norm_smul_inv_norm hδ
  set L : StrongDual ℝ (Space d) := innerSL ℝ u with hL
  have hLn : ‖L‖ = 1 := by rw [hL, innerSL_apply_norm, hun]
  have hmapL : (stdGaussian (Space d)).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hLn]
    simp
  have hmh : Measurable (fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) := by fun_prop
  have hkey : ∀ z : Space d, inner ℝ δ (x + σ • z - x) / (σ * ‖δ‖) = L z := by
    intro z
    simp only [hL, innerSL_apply_apply, hu, inner_smul_left, add_sub_cancel_left,
      inner_smul_right, starRingEnd_apply, star_trivial]
    field_simp
  have hpre : (fun z : Space d => x + σ • z) ⁻¹'
      ((fun z : Space d => inner ℝ δ (z - x) / (σ * ‖δ‖)) ⁻¹' S) = L ⁻¹' S := by
    ext z
    simp only [Set.mem_preimage]
    rw [hkey z]
  unfold gaussNoise
  rw [Measure.map_apply (by fun_prop) (hmh hS), hpre,
    ← Measure.map_apply L.continuous.measurable hS, hmapL]

open MeasureTheory ProbabilityTheory Cohen2019.Tight in
theorem solution {d : ℕ} (x δ : Space d) (σ pA : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise (x + δ) σ (setA x δ σ pA)).toReal = Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal pA - ‖δ‖ / σ) := by
  have hnδ : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hk : 0 < σ * ‖δ‖ := mul_pos hσ hnδ
  set c := Cohen2019.Robust.PhiInvReal pA with hc
  have hmul : (c - ‖δ‖ / σ) * (σ * ‖δ‖) = σ * ‖δ‖ * c - ‖δ‖ ^ 2 := by
    field_simp
  have hset : setA x δ σ pA =
      (fun z : Space d => inner ℝ δ (z - (x + δ)) / (σ * ‖δ‖)) ⁻¹' Set.Iic (c - ‖δ‖ / σ) := by
    ext z
    have hsplit : inner ℝ δ (z - x) = inner ℝ δ (z - (x + δ)) + ‖δ‖ ^ 2 := by
      have : z - x = (z - (x + δ)) + δ := by abel
      rw [this, inner_add_right, real_inner_self_eq_norm_sq]
    simp only [setA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    rw [div_le_iff₀ hk, hmul, hsplit, ← hc]
    constructor <;> intro h <;> linarith
  rw [hset, pxa_law (x + δ) δ σ hσ hδ (Set.Iic (c - ‖δ‖ / σ)) measurableSet_Iic]
  unfold Cohen2019.Robust.Phi
  rw [cdf_eq_real]
  rfl
