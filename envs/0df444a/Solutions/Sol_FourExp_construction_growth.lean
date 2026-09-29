-- Prove2me | solution 1 for FourExp.construction_growth
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T19:24:24.686461+00:00
-- url     : https://prove2.me/submissions/c2ad50d4-e3a8-4aac-aa82-e93ff0566a11

import Mathlib

open Filter Topology

namespace FourExpGrow

/-- The growing majorant of the construction. -/
noncomputable def A (x : ℝ) : ℝ :=
  if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x)

/-- Its companion with the reciprocal root. -/
noncomputable def B (x : ℝ) : ℝ :=
  if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x)

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [show (1:ℝ) = Real.log (Real.exp 1) by simp]
  refine Real.log_lt_log (Real.exp_pos 1) ?_
  have := Real.exp_one_lt_d9
  linarith

lemma log_three_lt_two : Real.log 3 < 2 := by
  rw [show (2:ℝ) = Real.log (Real.exp 2) by simp]
  refine Real.log_lt_log (by norm_num) ?_
  have h := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

lemma log_four_lt : Real.log 4 < 1.4 := by
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4]; linarith

lemma one_le_sqrt_log_three : 1 ≤ Real.sqrt (Real.log 3) :=
  Real.one_le_sqrt.2 one_lt_log_three.le

lemma sqrt_log_three_le : Real.sqrt (Real.log 3) ≤ 1.5 := by
  rw [show (1.5:ℝ) = Real.sqrt (1.5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have := log_three_lt_two; norm_num; linarith

lemma sqrt_log_four_le : Real.sqrt (Real.log 4) ≤ 1.19 := by
  rw [show (1.19:ℝ) = Real.sqrt (1.19 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  have := log_four_lt; norm_num; linarith

lemma nine_div_bounds : 6 ≤ 9 / Real.sqrt (Real.log 3) ∧ 9 / Real.sqrt (Real.log 3) ≤ 9 := by
  have h3 := one_le_sqrt_log_three
  have h3u := sqrt_log_three_le
  have hs3 : (0:ℝ) < Real.sqrt (Real.log 3) := by linarith
  constructor
  · rw [le_div_iff₀ hs3]; nlinarith
  · rw [div_le_iff₀ hs3]; nlinarith

lemma sqrt_log_lt_self {x : ℝ} (hx : 3 < x) : Real.sqrt (Real.log x) < Real.log x := by
  have h1 : 1 < Real.log x := by
    have := one_lt_log_three
    have := Real.log_lt_log (by norm_num : (0:ℝ) < 3) hx
    linarith
  calc Real.sqrt (Real.log x) < Real.sqrt (Real.log x ^ 2) := by
        refine Real.sqrt_lt_sqrt (Real.log_nonneg (by linarith)) ?_
        nlinarith
    _ = Real.log x := Real.sqrt_sq (by linarith)

lemma one_le_sqrt_log {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.sqrt (Real.log x) := by
  refine Real.one_le_sqrt.2 ?_
  have := one_lt_log_three
  have := Real.log_le_log (by norm_num) hx
  linarith

lemma sqrt_log_pos {x : ℝ} (hx : 3 ≤ x) : 0 < Real.sqrt (Real.log x) :=
  lt_of_lt_of_le zero_lt_one (one_le_sqrt_log hx)

/-- On `[3, ∞)` the product form is strictly increasing. -/
lemma strictMonoOn_A_right : StrictMonoOn (fun x : ℝ => x ^ 2 * Real.sqrt (Real.log x)) (Set.Ici 3) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1 : x ^ 2 < y ^ 2 := by nlinarith
  have h2 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log y) :=
    Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy.le)
  have h3 : 0 < Real.sqrt (Real.log x) := sqrt_log_pos hx
  calc x ^ 2 * Real.sqrt (Real.log x) < y ^ 2 * Real.sqrt (Real.log x) := by
        exact mul_lt_mul_of_pos_right h1 h3
    _ ≤ y ^ 2 * Real.sqrt (Real.log y) := by
        refine mul_le_mul_of_nonneg_left h2 (by positivity)

/-- On `[3, ∞)` the quotient form is strictly increasing. -/
lemma strictMonoOn_B_right : StrictMonoOn (fun x : ℝ => x ^ 2 / Real.sqrt (Real.log x)) (Set.Ici 3) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : (0:ℝ) < x := by linarith
  have hy0 : (0:ℝ) < y := by linarith
  have hlx : 0 < Real.log x := by
    have := one_lt_log_three
    have := Real.log_le_log (by norm_num) hx
    linarith
  have hly : 0 < Real.log y := by
    have := one_lt_log_three
    have := Real.log_le_log (by norm_num) hy
    linarith
  have hsx : 0 < Real.sqrt (Real.log x) := sqrt_log_pos hx
  have hsy : 0 < Real.sqrt (Real.log y) := sqrt_log_pos hy
  rw [div_lt_div_iff₀ hsx hsy]
  -- `log t / t` is antitone past `e`, so `log y / log x ≤ y / x`
  have he : Real.exp 1 ≤ x := by
    have := Real.exp_one_lt_d9; linarith
  have hant := Real.log_div_self_antitoneOn (Set.mem_Ici.2 he)
    (Set.mem_Ici.2 (he.trans hxy.le)) hxy.le
  simp only at hant
  have hratio : Real.log y * x ≤ Real.log x * y := by
    rw [div_le_div_iff₀ hy0 hx0] at hant
    linarith
  -- hence `√log y · x ≤ √log x · y` after taking roots
  have hsq : Real.sqrt (Real.log y) * x ≤ Real.sqrt (Real.log x) * y := by
    have h1 : (Real.sqrt (Real.log y) * x) ^ 2 ≤ (Real.sqrt (Real.log x) * y) ^ 2 := by
      have e1 : (Real.sqrt (Real.log y)) ^ 2 = Real.log y := Real.sq_sqrt hly.le
      have e2 : (Real.sqrt (Real.log x)) ^ 2 = Real.log x := Real.sq_sqrt hlx.le
      calc (Real.sqrt (Real.log y) * x) ^ 2 = Real.log y * x ^ 2 := by rw [mul_pow, e1]
        _ = (Real.log y * x) * x := by ring
        _ ≤ (Real.log x * y) * y := by
            refine mul_le_mul hratio hxy.le hx0.le (by positivity)
        _ = Real.log x * y ^ 2 := by ring
        _ = (Real.sqrt (Real.log x) * y) ^ 2 := by rw [mul_pow, e2]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
  calc x ^ 2 * Real.sqrt (Real.log y) = x * (Real.sqrt (Real.log y) * x) := by ring
    _ ≤ x * (Real.sqrt (Real.log x) * y) := mul_le_mul_of_nonneg_left hsq hx0.le
    _ = (x * y) * Real.sqrt (Real.log x) := by ring
    _ < (y * y) * Real.sqrt (Real.log x) := by
        refine mul_lt_mul_of_pos_right ?_ hsx
        exact mul_lt_mul_of_pos_right hxy hy0
    _ = y ^ 2 * Real.sqrt (Real.log x) := by ring

lemma A_at_three : A 3 = 9 * Real.sqrt (Real.log 3) := by simp [A]

lemma B_at_three : B 3 = 9 / Real.sqrt (Real.log 3) := by simp [B]

lemma strictMono_A : StrictMono A := by
  intro x y hxy
  by_cases hx : x ≤ 3
  · by_cases hy : y ≤ 3
    · simp only [A, if_pos hx, if_pos hy]; linarith
    · push_neg at hy
      have h1 : A x ≤ 9 * Real.sqrt (Real.log 3) := by
        simp only [A, if_pos hx]; linarith
      have h2 : (3:ℝ) ^ 2 * Real.sqrt (Real.log 3) < y ^ 2 * Real.sqrt (Real.log y) :=
        strictMonoOn_A_right (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy
      simp only [A, if_pos hx, if_neg (not_le.2 hy)]
      norm_num at h2
      linarith
  · push_neg at hx
    have hy : ¬ y ≤ 3 := by push_neg; linarith
    simp only [A, if_neg (not_le.2 hx), if_neg hy]
    exact strictMonoOn_A_right (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 (by linarith)) hxy

lemma strictMono_B : StrictMono B := by
  intro x y hxy
  by_cases hx : x ≤ 3
  · by_cases hy : y ≤ 3
    · simp only [B, if_pos hx, if_pos hy]; linarith
    · push_neg at hy
      have h1 : B x ≤ 9 / Real.sqrt (Real.log 3) := by
        simp only [B, if_pos hx]; linarith
      have h2 : (3:ℝ) ^ 2 / Real.sqrt (Real.log 3) < y ^ 2 / Real.sqrt (Real.log y) :=
        strictMonoOn_B_right (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy
      simp only [B, if_pos hx, if_neg (not_le.2 hy)]
      norm_num at h2
      linarith
  · push_neg at hx
    have hy : ¬ y ≤ 3 := by push_neg; linarith
    simp only [B, if_neg (not_le.2 hx), if_neg hy]
    exact strictMonoOn_B_right (Set.mem_Ici.2 hx.le) (Set.mem_Ici.2 (by linarith)) hxy

lemma le_A {x : ℝ} (hx : 3 ≤ x) : x ≤ A x := by
  have h3 := one_le_sqrt_log_three
  by_cases hle : x ≤ 3
  · simp only [A, if_pos hle]; nlinarith
  · push_neg at hle
    simp only [A, if_neg (not_le.2 hle)]
    have h1 : 1 ≤ Real.sqrt (Real.log x) := one_le_sqrt_log hx
    nlinarith

lemma le_B {x : ℝ} (hx : 3 ≤ x) : x ≤ B x := by
  obtain ⟨hc6, -⟩ := nine_div_bounds
  by_cases hle : x ≤ 3
  · simp only [B, if_pos hle]; linarith
  · push_neg at hle
    simp only [B, if_neg (not_le.2 hle)]
    have hlx : 1 < Real.log x := by
      have := one_lt_log_three
      have := Real.log_lt_log (by norm_num : (0:ℝ) < 3) hle
      linarith
    have hsx : 0 < Real.sqrt (Real.log x) := sqrt_log_pos hx
    have hs : Real.sqrt (Real.log x) ≤ x := by
      have h1 := sqrt_log_lt_self hle
      have h2 := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < x)
      linarith
    rw [le_div_iff₀ hsx]
    nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0:ℝ) ≤ x)]

lemma tendsto_A : Tendsto A atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (3:ℝ)] with x hx using le_A hx

lemma tendsto_B : Tendsto B atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (3:ℝ)] with x hx using le_B hx

lemma B_le_A (x : ℝ) : B x ≤ A x := by
  by_cases hx : x ≤ 3
  · simp only [A, B, if_pos hx]
    obtain ⟨-, hc9⟩ := nine_div_bounds
    have h1 := one_le_sqrt_log_three
    nlinarith
  · push_neg at hx
    simp only [A, B, if_neg (not_le.2 hx)]
    have h1 : 1 ≤ Real.sqrt (Real.log x) := one_le_sqrt_log hx.le
    have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt (by
        have := one_lt_log_three
        have := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx.le
        linarith)
    rw [div_le_iff₀ (by linarith), mul_assoc, hsq]
    have hlx : 1 ≤ Real.log x := by nlinarith
    nlinarith [sq_nonneg x]

lemma A_step (x : ℝ) (hx : 0 < x) : A (x + 1) ≤ 3 * A x := by
  have h3 := one_le_sqrt_log_three
  by_cases h1 : x + 1 ≤ 3
  · have hx3 : x ≤ 3 := by linarith
    simp only [A, if_pos h1, if_pos hx3]
    linarith
  · push_neg at h1
    by_cases hx3 : x ≤ 3
    · -- `2 < x ≤ 3`, so `3 < x + 1 ≤ 4`
      have hx2 : 2 < x := by linarith
      simp only [A, if_neg (not_le.2 h1), if_pos hx3]
      have hsq : (x + 1) ^ 2 ≤ 16 := by nlinarith
      have hlog : Real.sqrt (Real.log (x + 1)) ≤ Real.sqrt (Real.log 4) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (by linarith))
      have h4 := sqrt_log_four_le
      have hpos : 0 ≤ Real.sqrt (Real.log (x + 1)) := Real.sqrt_nonneg _
      nlinarith
    · push_neg at hx3
      have hxx : ¬ x ≤ 3 := not_le.2 hx3
      simp only [A, if_neg (not_le.2 h1), if_neg hxx]
      have hsq : (x + 1) ^ 2 ≤ 16 / 9 * x ^ 2 := by nlinarith
      have hlog : Real.sqrt (Real.log (x + 1)) ≤ Real.sqrt 2 * Real.sqrt (Real.log x) := by
        rw [← Real.sqrt_mul (by norm_num)]
        refine Real.sqrt_le_sqrt ?_
        have h2 : Real.log (x + 1) ≤ Real.log (x ^ 2) :=
          Real.log_le_log (by linarith) (by nlinarith)
        rw [Real.log_pow] at h2; push_cast at h2; linarith
      have hs2 : Real.sqrt 2 ≤ 1.415 := by
        rw [show (1.415:ℝ) = Real.sqrt (1.415 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hsx : 1 ≤ Real.sqrt (Real.log x) := one_le_sqrt_log hx3.le
      have hpos : 0 ≤ Real.sqrt (Real.log (x + 1)) := Real.sqrt_nonneg _
      have hprod : (x + 1) ^ 2 * Real.sqrt (Real.log (x + 1))
          ≤ (16 / 9 * x ^ 2) * (Real.sqrt 2 * Real.sqrt (Real.log x)) :=
        mul_le_mul hsq hlog hpos (by positivity)
      have hconst : (16 / 9 : ℝ) * Real.sqrt 2 ≤ 3 := by nlinarith
      have hfin : (16 / 9 * x ^ 2) * (Real.sqrt 2 * Real.sqrt (Real.log x))
          ≤ 3 * (x ^ 2 * Real.sqrt (Real.log x)) := by
        have h := mul_le_mul_of_nonneg_right hconst
          (by positivity : (0:ℝ) ≤ x ^ 2 * Real.sqrt (Real.log x))
        calc (16 / 9 * x ^ 2) * (Real.sqrt 2 * Real.sqrt (Real.log x))
            = (16 / 9 * Real.sqrt 2) * (x ^ 2 * Real.sqrt (Real.log x)) := by ring
          _ ≤ 3 * (x ^ 2 * Real.sqrt (Real.log x)) := h
      linarith

lemma B_step (x : ℝ) (hx : 0 < x) : B (x + 1) ≤ 3 * B x := by
  obtain ⟨hc6, hc9⟩ := nine_div_bounds
  have h3 := one_le_sqrt_log_three
  have h3u := sqrt_log_three_le
  have hs3 : (0:ℝ) < Real.sqrt (Real.log 3) := by linarith
  by_cases h1 : x + 1 ≤ 3
  · have hx3 : x ≤ 3 := by linarith
    simp only [B, if_pos h1, if_pos hx3]
    linarith
  · push_neg at h1
    by_cases hx3 : x ≤ 3
    · have hx2 : 2 < x := by linarith
      simp only [B, if_neg (not_le.2 h1), if_pos hx3]
      have hs1 : 0 < Real.sqrt (Real.log (x + 1)) := sqrt_log_pos (by linarith)
      have hlog : Real.sqrt (Real.log 3) ≤ Real.sqrt (Real.log (x + 1)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith))
      have hsq : (x + 1) ^ 2 ≤ 16 := by nlinarith
      have hle : (x + 1) ^ 2 / Real.sqrt (Real.log (x + 1)) ≤ 16 / Real.sqrt (Real.log 3) := by
        gcongr
      have h16 : (16:ℝ) / Real.sqrt (Real.log 3) = 16 / 9 * (9 / Real.sqrt (Real.log 3)) := by
        field_simp
      rw [h16] at hle
      linarith
    · push_neg at hx3
      have hxx : ¬ x ≤ 3 := not_le.2 hx3
      simp only [B, if_neg (not_le.2 h1), if_neg hxx]
      have hsx : 0 < Real.sqrt (Real.log x) := sqrt_log_pos hx3.le
      have hs1 : 0 < Real.sqrt (Real.log (x + 1)) := sqrt_log_pos (by linarith)
      have hlog : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x + 1)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (by linarith))
      have hsq : (x + 1) ^ 2 ≤ 3 * x ^ 2 := by nlinarith
      calc (x + 1) ^ 2 / Real.sqrt (Real.log (x + 1))
          ≤ (x + 1) ^ 2 / Real.sqrt (Real.log x) := by gcongr
        _ ≤ 3 * x ^ 2 / Real.sqrt (Real.log x) := by gcongr
        _ = 3 * (x ^ 2 / Real.sqrt (Real.log x)) := by ring

end FourExpGrow

theorem solution (k : ℝ) (hk : 0 < k) :
    StrictMono (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x))) ∧
    StrictMono (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x))) ∧
    Tendsto (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x))) atTop atTop ∧
    Tendsto (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x))) atTop atTop ∧
    (∀ x : ℝ, 0 < x → k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x)) ≤ k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x))) ∧
    (∀ x : ℝ, 0 < x → k * (if (x + 1) ≤ 3 then (x + 1) - 3 + 9 * Real.sqrt (Real.log 3) else (x + 1) ^ 2 * Real.sqrt (Real.log (x + 1))) ≤ 3 * (k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x)))) ∧
    (∀ x : ℝ, 0 < x → k * (if (x + 1) ≤ 3 then (x + 1) - 3 + 9 / Real.sqrt (Real.log 3) else (x + 1) ^ 2 / Real.sqrt (Real.log (x + 1))) ≤ 3 * (k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x)))) := by
  refine ⟨fun x y h => mul_lt_mul_of_pos_left (FourExpGrow.strictMono_A h) hk,
    fun x y h => mul_lt_mul_of_pos_left (FourExpGrow.strictMono_B h) hk,
    Filter.Tendsto.const_mul_atTop hk FourExpGrow.tendsto_A,
    Filter.Tendsto.const_mul_atTop hk FourExpGrow.tendsto_B,
    fun x _ => mul_le_mul_of_nonneg_left (FourExpGrow.B_le_A x) hk.le,
    fun x hx => ?_, fun x hx => ?_⟩
  · have h := mul_le_mul_of_nonneg_left (FourExpGrow.A_step x hx) hk.le
    calc k * FourExpGrow.A (x + 1) ≤ k * (3 * FourExpGrow.A x) := h
      _ = 3 * (k * FourExpGrow.A x) := by ring
  · have h := mul_le_mul_of_nonneg_left (FourExpGrow.B_step x hx) hk.le
    calc k * FourExpGrow.B (x + 1) ≤ k * (3 * FourExpGrow.B x) := h
      _ = 3 * (k * FourExpGrow.B x) := by ring
