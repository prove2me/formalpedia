-- Prove2me | solution 1 for BesbesZeevi.Nonparametric.nonparametric_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T12:58:35.611405+00:00
-- url     : https://prove2.me/submissions/7ed13ec2-e002-4076-82e0-84e69ffdceb4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm
import Theorems.Thm_BesbesZeevi_Nonparametric_step4_regret_bound
set_option autoImplicit false

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

theorem nrb_tuning_rate (T c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
      uSeq n (τ n) (κ n) + τ n ≤ K * Real.sqrt (Real.log n) / (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hc := htune.c_pos
  have hc' : 0 < c' := lt_of_lt_of_le hc htune.c_le
  have hl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have hq0 : 0 < Real.sqrt (c / c') := Real.sqrt_pos.mpr (div_pos hc hc')
  refine ⟨1 / c + 1 / Real.sqrt (c / c') + c' / Real.sqrt (Real.log 2), by positivity,
    fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hapos : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hneg : (n : ℝ) ^ (-(1 / 4 : ℝ)) = ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg hnpos.le _
  have ha4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
  have hτl := htune.tau_lower n hn1
  have hτu := htune.tau_upper n hn1
  have hκl := htune.kappa_lower n hn1
  have hκu := htune.kappa_upper n hn1
  rw [hneg] at hτl hτu
  have hτpos := htune.tau_pos n hn1
  set a := (n : ℝ) ^ (1 / 4 : ℝ) with ha
  have hκpos : 0 < (κ n : ℝ) := lt_of_lt_of_le (by positivity) hκl
  have hs : Real.sqrt (Real.log 2) ≤ Real.sqrt (Real.log n) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) hnR)
  set l2 := Real.sqrt (Real.log 2) with hl2def
  set s := Real.sqrt (Real.log n) with hsdef
  have hspos : 0 < s := lt_of_lt_of_le hl2 hs
  -- bound on 1/κ
  have h1 : 1 / (κ n : ℝ) ≤ (1 / c) / a := by
    rw [div_div, div_le_div_iff₀ hκpos (by positivity)]; linarith
  -- bound on 1/√(nτ/κ)
  have e3 : c * a ^ 3 ≤ (n : ℝ) * τ n := by
    rw [← ha4]
    have : c * a ^ 3 = a ^ 4 * (c * a⁻¹) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hτl (by positivity)
  have e1 : (c / c') * a ^ 2 * (κ n : ℝ) ≤ c * a ^ 3 := by
    calc (c / c') * a ^ 2 * (κ n : ℝ) ≤ (c / c') * a ^ 2 * (c' * a) := by
          exact mul_le_mul_of_nonneg_left hκu (by positivity)
      _ = c * a ^ 3 := by field_simp
  have hq : (c / c') * a ^ 2 ≤ (n : ℝ) * (τ n / (κ n : ℝ)) := by
    rw [← mul_div_assoc, le_div_iff₀ hκpos]; linarith
  have hsq : Real.sqrt (c / c') * a ≤ Real.sqrt ((n : ℝ) * (τ n / (κ n : ℝ))) := by
    rw [show Real.sqrt (c / c') * a = Real.sqrt ((c / c') * a ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hapos.le]]
    exact Real.sqrt_le_sqrt hq
  have h2 : 1 / Real.sqrt ((n : ℝ) * (τ n / (κ n : ℝ))) ≤ (1 / Real.sqrt (c / c')) / a := by
    rw [div_div]; exact one_div_le_one_div_of_le (by positivity) hsq
  have hmax : max (1 / (κ n : ℝ)) (1 / Real.sqrt ((n : ℝ) * (τ n / (κ n : ℝ))))
      ≤ (1 / c + 1 / Real.sqrt (c / c')) / a := by
    have p1 : 0 ≤ (1 / c) / a := by positivity
    have p2 : 0 ≤ (1 / Real.sqrt (c / c')) / a := by positivity
    rw [add_div]
    exact max_le (by linarith) (by linarith)
  have hu : uSeq n (τ n) (κ n) ≤ s * ((1 / c + 1 / Real.sqrt (c / c')) / a) := by
    unfold uSeq
    exact mul_le_mul_of_nonneg_left hmax (Real.sqrt_nonneg _)
  have hratio : 1 ≤ s / l2 := by rw [le_div_iff₀ hl2]; linarith
  have hτ2 : τ n ≤ c' / l2 * s / a := by
    have : c' / l2 * s / a = c' * a⁻¹ * (s / l2) := by field_simp
    rw [this]
    calc τ n ≤ c' * a⁻¹ := hτu
      _ = c' * a⁻¹ * 1 := by ring
      _ ≤ c' * a⁻¹ * (s / l2) := mul_le_mul_of_nonneg_left hratio (by positivity)
  have hK : (1 / c + 1 / Real.sqrt (c / c') + c' / l2) * s / a
      = s * ((1 / c + 1 / Real.sqrt (c / c')) / a) + c' / l2 * s / a := by ring
  rw [hK]; linarith


end BesbesZeevi.Nonparametric

section NRBSolution

open BesbesZeevi.Nonparametric

theorem solution (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ n : ℕ, 2 ≤ n → ∀ lam : ℝ → ℝ, L.Mem P lam →
        regret P lam x T n (τ n) (κ n) N ≤ C * Real.sqrt (Real.log n) / (n : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C₁₂, hC, h4⟩ := step4_regret_bound P L x T hx hT c c' τ κ htune
  obtain ⟨K, hK, hrate⟩ := nrb_tuning_rate T c c' τ κ htune
  refine ⟨C₁₂ * K, by positivity, fun Ω _ N hN n hn lam hlam => ?_⟩
  calc regret P lam x T n (τ n) (κ n) N ≤ C₁₂ * (uSeq n (τ n) (κ n) + τ n) :=
        h4 Ω N hN n (by omega) lam hlam
    _ ≤ C₁₂ * (K * Real.sqrt (Real.log n) / (n : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hrate n hn) hC.le
    _ = C₁₂ * K * Real.sqrt (Real.log n) / (n : ℝ) ^ (1 / 4 : ℝ) := by ring

end NRBSolution
