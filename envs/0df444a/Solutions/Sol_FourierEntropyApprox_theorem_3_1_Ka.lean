-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_1_Ka
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:06.356526+00:00
-- url     : https://prove2.me/submissions/be1030b9-958b-4a5d-896e-ba516c10d65f

import Mathlib
import Definitions.Def_FourierEntropyApprox_Ka

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Ka
open Real

/-- y^a ≤ 2^a a^a e^{-a} e^{y/2} for y ≥ 0, a ≥ 0. -/
lemma pt (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) :
    y ^ a ≤ 2 ^ a * (a ^ a * Real.exp (-a)) * Real.exp (y / 2) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [Real.rpow_zero, neg_zero, Real.exp_zero, mul_one, one_mul]
    exact Real.one_le_exp (by linarith)
  have h1 : (y / 2 / a) ≤ Real.exp (y / 2 / a - 1) := by
    have := Real.add_one_le_exp (y / 2 / a - 1); linarith
  have h2 : (y / 2 / a) ^ a ≤ Real.exp (y / 2 / a - 1) ^ a :=
    Real.rpow_le_rpow (by positivity) h1 ha.le
  rw [← Real.exp_mul] at h2
  have h3 : (y / 2 / a - 1) * a = y / 2 - a := by field_simp
  rw [h3, Real.div_rpow (by positivity) ha.le, Real.div_rpow hy (by norm_num) ] at h2
  have hp : (0:ℝ) < a ^ a := Real.rpow_pos_of_pos ha _
  have hp2 : (0:ℝ) < 2 ^ a := Real.rpow_pos_of_pos (by norm_num) _
  rw [div_le_iff₀ hp, div_le_iff₀ hp2] at h2
  have : Real.exp (y / 2 - a) = Real.exp (y/2) * Real.exp (-a) := by
    rw [← Real.exp_add]; ring_nf
  rw [this] at h2
  nlinarith [h2]

lemma gamma_lb (a : ℝ) (ha : 0 ≤ a) : a ^ a * Real.exp (-a) ≤ Real.exp 1 * Real.Gamma (a + 1) := by
  have hpos : 0 < a + 1 := by linarith
  rw [Real.Gamma_eq_integral hpos]
  have hint := Real.GammaIntegral_convergent hpos
  have hsub : Set.Ioc a (a + 1) ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Ioc, Set.mem_Ioi] at *; linarith [hx.1]
  have h1 : ∫ x in Set.Ioc a (a+1), Real.exp (-x) * x ^ (a + 1 - 1) ≤
      ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (a + 1 - 1) := by
    apply MeasureTheory.setIntegral_mono_set hint
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt hx) _)
    · exact Filter.Eventually.of_forall hsub
  have h2 : ∫ x in Set.Ioc a (a+1), (a ^ a * Real.exp (-(a+1))) ≤
      ∫ x in Set.Ioc a (a+1), Real.exp (-x) * x ^ (a + 1 - 1) := by
    apply MeasureTheory.setIntegral_mono_on
    · exact MeasureTheory.integrableOn_const (by simp) enorm_ne_top
    · exact hint.mono_set hsub
    · exact measurableSet_Ioc
    · intro x hx
      have hx0 : a ≤ x := hx.1.le
      have e1 : Real.exp (-(a+1)) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith [hx.2])
      have e2 : a ^ a ≤ x ^ (a + 1 - 1) := by
        rw [add_sub_cancel_right]; exact Real.rpow_le_rpow ha hx0 ha
      have := Real.rpow_nonneg ha a
      calc a ^ a * Real.exp (-(a+1)) ≤ x ^ (a + 1 - 1) * Real.exp (-x) :=
            mul_le_mul e2 e1 (Real.exp_pos _).le (le_trans this e2)
        _ = _ := mul_comm _ _
  simp only [MeasureTheory.setIntegral_const, Real.volume_real_Ioc, smul_eq_mul] at h2
  have : a + 1 - a = 1 := by ring
  rw [max_eq_left (by linarith), this, one_mul] at h2
  have h3 := h2.trans h1
  rw [Real.exp_neg, Real.exp_add] at h3
  have he := Real.exp_pos 1
  have he2 := Real.exp_pos a
  have : a ^ a * Real.exp (-a) = Real.exp 1 * (a ^ a * (Real.exp a * Real.exp 1)⁻¹) := by
    rw [Real.exp_neg]; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left h3 he.le

lemma exp_half_lt : Real.exp (1/2) < 2 := by
  have h : Real.exp (1/2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1/2)]

lemma major_eq (j : ℕ) : ((2:ℝ) ^ (j+1))⁻¹ * Real.exp ((((j+1:ℕ):ℝ) + 3) / 2) =
    (Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j := by
  have h : Real.exp ((((j+1:ℕ):ℝ) + 3) / 2) = Real.exp 2 * Real.exp (1/2) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [h, div_pow, pow_succ]; field_simp

lemma summ : Summable (fun j : ℕ => (Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j) := by
  apply Summable.mul_left
  apply summable_geometric_of_lt_one (by positivity)
  have := exp_half_lt; linarith

end FourierEntropyApprox.Dev.Ka

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Ka in
theorem chk_theorem_3_1_Ka :
    (∀ a : ℝ, 0 ≤ a → Summable (fun j : ℕ => KaTerm a (j + 1))) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 ≤ a → Ka a ≤ c * (2 : ℝ) ^ a * Real.Gamma (a + 1) := by
  have key : ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ, KaTerm a (j + 1) ≤
      2 ^ a * (a ^ a * Real.exp (-a)) * ((Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j) := by
    intro a ha j
    unfold KaTerm
    rw [← major_eq]
    have := pt a (((j+1:ℕ):ℝ) + 3) ha (by positivity)
    have hp : (0:ℝ) < ((2:ℝ) ^ (j+1))⁻¹ := by positivity
    calc _ ≤ ((2:ℝ) ^ (j+1))⁻¹ * (2 ^ a * (a ^ a * Real.exp (-a)) * Real.exp ((((j+1:ℕ):ℝ) + 3) / 2)) :=
          mul_le_mul_of_nonneg_left this hp.le
      _ = _ := by ring
  have hsum : ∀ a : ℝ, 0 ≤ a → Summable (fun j : ℕ => KaTerm a (j + 1)) := by
    intro a ha
    refine Summable.of_nonneg_of_le (fun j => ?_) (key a ha) (summ.mul_left _)
    unfold KaTerm
    have : (0:ℝ) ≤ (((j+1:ℕ):ℝ) + 3) ^ a := Real.rpow_nonneg (by positivity) _
    positivity
  refine ⟨hsum, Real.exp 1 * ∑' j : ℕ, (Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j + 1, ?_, ?_⟩
  · have : 0 ≤ ∑' j : ℕ, (Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j := tsum_nonneg (fun j => by positivity)
    positivity
  intro a ha
  have h1 : Ka a ≤ ∑' j : ℕ, 2 ^ a * (a ^ a * Real.exp (-a)) * ((Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j) :=
    Summable.tsum_le_tsum (key a ha) (hsum a ha) (summ.mul_left _)
  rw [tsum_mul_left] at h1
  set S := ∑' j : ℕ, (Real.exp 2 / 2) * (Real.exp (1/2) / 2) ^ j with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun j => by positivity)
  have hg := gamma_lb a ha
  have h2pos : (0:ℝ) < 2 ^ a := Real.rpow_pos_of_pos (by norm_num) _
  have hG : 0 ≤ Real.Gamma (a + 1) := (Real.Gamma_pos_of_pos (by linarith)).le
  have h3 : 2 ^ a * (a ^ a * Real.exp (-a)) * S ≤ 2 ^ a * (Real.exp 1 * Real.Gamma (a+1)) * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg h2pos.le) hS0
  have h4 : 2 ^ a * (Real.exp 1 * Real.Gamma (a+1)) * S
      = (Real.exp 1 * S) * 2 ^ a * Real.Gamma (a+1) := by ring
  have h5 : 0 ≤ 2 ^ a * Real.Gamma (a+1) := by positivity
  nlinarith [h1, h3, h4]

end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_1_Ka := @FourierEntropyApprox.chk_theorem_3_1_Ka
