-- Prove2me | solution 2 for DbarRegularity.maximalFunction_weakType_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:25:38.05854+00:00
-- url     : https://prove2.me/submissions/931979a2-1766-4707-a03e-80d2298b1360

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Covering.Vitali
import Theorems.Thm_DbarRegularity_volume_ball_mul
import Theorems.Thm_DbarRegularity_maximalFunction_exists_radius_bound



namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal NNReal

/-- Weak type `(1,1)` bound for the Hardy–Littlewood maximal function, with constant `5^d`. -/
theorem maximalFunction_weakType_one (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ x, ‖f x‖ₑ := by
  by_cases hS : ∫⁻ y, ‖f y‖ₑ = ⊤
  · rw [hS, ENNReal.mul_top]
    · exact le_top
    · exact ENNReal.div_ne_zero.2 ⟨pow_ne_zero _ (by norm_num), ENNReal.coe_ne_top⟩
  obtain ⟨R, hR⟩ := maximalFunction_exists_radius_bound d f α hα hS
  set E := {x | (α : ℝ≥0∞) < maximalFunction f x}
  choose! ρ hρ0 hρR hρ using hR
  obtain ⟨u, huE, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    E id ρ R (fun a ha => hρR a ha) 5 (by norm_num)
  have hu : u.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun a ha => nonempty_ball.2 (hρ0 a (huE ha)))
  have hsub : E ⊆ ⋃ b ∈ u, ball b (5 * ρ b) := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact mem_biUnion hb (hab (mem_ball_self (hρ0 a ha)))
  haveI : Countable u := hu.to_subtype
  have hvol : ∀ b ∈ u, volume (ball b (5 * ρ b)) ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ball b (ρ b), ‖f y‖ₑ := by
    intro b hb
    have hV := hρ b (huE hb)
    calc volume (ball b (5 * ρ b)) = (5 : ℝ≥0∞) ^ d * volume (ball b (ρ b)) := by
          rw [volume_ball_mul d b (hρ0 b (huE hb)) 5 (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ (5 : ℝ≥0∞) ^ d * ((∫⁻ y in ball b (ρ b), ‖f y‖ₑ) / α) := by
          gcongr
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hα.ne'))
            (Or.inl ENNReal.coe_ne_top), mul_comm]
          exact hV.le
      _ = _ := by rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
  calc volume E ≤ volume (⋃ b ∈ u, ball b (5 * ρ b)) := measure_mono hsub
    _ ≤ ∑' b : u, volume (ball (b : EuclideanSpace ℝ (Fin d)) (5 * ρ b)) :=
        measure_biUnion_le _ hu _
    _ ≤ ∑' b : u, (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ball (b : EuclideanSpace ℝ (Fin d)) (ρ b),
          ‖f y‖ₑ := ENNReal.tsum_le_tsum fun b => hvol b b.2
    _ = (5 : ℝ≥0∞) ^ d / α * ∫⁻ y in ⋃ b : u, ball (b : EuclideanSpace ℝ (Fin d)) (ρ b),
          ‖f y‖ₑ := by
        rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun _ => measurableSet_ball)]
        intro i j hij
        exact hdisj i.2 j.2 (Subtype.coe_injective.ne hij)
    _ ≤ (5 : ℝ≥0∞) ^ d / α * ∫⁻ y, ‖f y‖ₑ := by
        exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem solution (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) (α : ℝ≥0)
    (hα : 0 < α) :
    volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤
      (5 : ℝ≥0∞) ^ d / α * ∫⁻ x, ‖f x‖ₑ :=
  maximalFunction_weakType_one d f α hα
