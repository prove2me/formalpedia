-- Prove2me | solution 1 for BianchiIX.partial_core_reciprocal_radial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:28:21.538199+00:00
-- url     : https://prove2.me/submissions/c983f860-ed45-462b-a287-91570ecea25b

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_difference_value_bound {α F R : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) :
    |2 / F - 2 / R| ≤ 2 * α ^ 2 * |F - R| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have Heq : 2 / F - 2 / R = -2 * (F - R) / (R * F) := by field_simp; ring
  rw [Heq, abs_div, abs_mul, abs_of_pos (mul_pos hR0 hF0)]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (2 * |F - R|) * (1 / R * (1 / F)) := by ring
    _ ≤ (2 * |F - R|) * (α * α) := by gcongr
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.reciprocal_difference_derivative_bound {α F R Θ p q D : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) (hq : |q| ≤ D / α ^ 2) :
    |-2 * p / F ^ 2 + 2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| ≤
      2 * α ^ 2 * |p| + 4 * D * α * |Θ| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have hFi2 : 1 / F ^ 2 ≤ α ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / F) hFi 2
  have HC : (F + R) / (R ^ 2 * F ^ 2) ≤ 2 * α ^ 3 := by
    calc
      _ = (1 / R) * (1 / R) * (1 / F) + (1 / R) * (1 / F) * (1 / F) := by field_simp
      _ ≤ α * α * α + α * α * α := by gcongr
      _ = _ := by ring
  calc
    _ ≤ |-2 * p / F ^ 2| + |2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| := abs_add_le _ _
    _ = (2 * |p|) * (1 / F ^ 2) + (2 * |Θ|) * ((F + R) / (R ^ 2 * F ^ 2)) * |q| := by
      rw [abs_div, abs_div]
      simp only [abs_mul, abs_neg, abs_of_pos hF0, abs_of_pos hR0,
        abs_of_pos (add_pos hF0 hR0), abs_pow]
      norm_num
      ring
    _ ≤ (2 * |p|) * α ^ 2 + (2 * |Θ|) * (2 * α ^ 3) * (D / α ^ 2) := by gcongr
    _ = _ := by field_simp; ring

end
end

private theorem BianchiIX.hasDerivAt_reciprocal_error {f k : ℝ → ℝ} {x df dk : ℝ}
    (hf : HasDerivAt f df x) (hk : HasDerivAt k dk x) (hf0 : f x ≠ 0) (hk0 : k x ≠ 0) :
    HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * (df - dk) / (f x) ^ 2 +
        2 * (f x - k x) * (f x + k x) * dk / ((k x) ^ 2 * (f x) ^ 2)) x := by
  have Hf : HasDerivAt (fun y => 2 / f y) (-2 * df / (f x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hf hf0 using 1
    ring
  have Hk : HasDerivAt (fun y => 2 / k y) (-2 * dk / (k x) ^ 2) x := by
    convert! (hasDerivAt_const x (2 : ℝ)).div hk hk0 using 1
    ring
  have H : HasDerivAt (fun y => 2 / f y - 2 / k y)
      (-2 * df / (f x) ^ 2 - (-2 * dk / (k x) ^ 2)) x := Hf.sub Hk
  convert! H using 1
  field_simp
  ring


/-- Reciprocal phase loses no amplitude power when the radial difference is differentiated first. -/
theorem solution {f k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x)
    (hklo : 2 / (K * r) ≤ k x) (hFlo : k x / 2 ≤ f x)
    (hvalue : |f x - k x| ≤ 16 * (U + P ^ 2 / k x))
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U + r * P) / r ^ 2) :
    DifferentiableAt ℝ (fun y => 2 / f y - 2 / k y) x ∧
      |f x - k x| ≤ 16 * K * (U + r * P ^ 2) ∧
      |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv (fun y => 2 / f y - 2 / k y) x| ≤
        (8 * C * K ^ 4 + 64 * K ^ 5) * (U + r * P) := by
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hKr : 0 < K * r := mul_pos hK0 hr.1
  have hk0 : 0 < k x := (div_pos (by norm_num) hKr).trans_le hklo
  have hF0 : 0 < f x := (half_pos hk0).trans_le hFlo
  have hkhalf : 1 / (K * r) ≤ k x / 2 := by
    have heq : 2 / (K * r) = 2 * (1 / (K * r)) := by ring
    rw [heq] at hklo
    linarith only [hklo]
  have hkα : 1 / (K * r) ≤ k x := hkhalf.trans (by linarith only [hk0])
  have hfα : 1 / (K * r) ≤ f x := hkhalf.trans hFlo
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ hKr).mp hkα]
  have he : |f x - k x| ≤ 16 * K * (U + r * P ^ 2) := hvalue.trans (by
    have H₁ := mul_le_mul_of_nonneg_left hK hU
    have H₂ := mul_le_mul_of_nonneg_left hki (sq_nonneg P)
    simp only [mul_one_div] at H₂
    nlinarith only [H₁, H₂])
  have HD := hasDerivAt_reciprocal_error hf.hasDerivAt hk.hasDerivAt hF0.ne' hk0.ne'
  refine ⟨HD.differentiableAt, he, ?_, ?_⟩
  · exact (reciprocal_difference_value_bound hKr hfα hkα).trans
      ((mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * (K * r) ^ 2)).trans_eq (by ring))
  · have hq : |deriv k x| ≤ K ^ 3 / (K * r) ^ 2 := hdk.trans_eq (by field_simp)
    have H := reciprocal_difference_derivative_bound hKr hfα hkα hq
      (Θ := f x - k x) (p := deriv f x - deriv k x)
    have H₁ : 2 * (K * r) ^ 2 * |deriv f x - deriv k x| ≤
        8 * C * K ^ 4 * (U + r * P) :=
      (mul_le_mul_of_nonneg_left hde (by positivity)).trans_eq (by field_simp; ring)
    have hPr : 0 ≤ P * r ∧ P * r ≤ 1 :=
      ⟨mul_nonneg hP.1 hr.1.le, (mul_le_mul_of_nonneg_right hP.2 hr.1.le).trans (by simpa using hr.2)⟩
    have hsmall : r * (U + r * P ^ 2) ≤ U + r * P := by
      nlinarith only [mul_le_mul_of_nonneg_left hr.2 hU,
        mul_le_mul_of_nonneg_right hPr.2 hPr.1]
    have H₂ : 4 * K ^ 3 * (K * r) * |f x - k x| ≤ 64 * K ^ 5 * (U + r * P) := by
      calc
        _ ≤ 4 * K ^ 3 * (K * r) * (16 * K * (U + r * P ^ 2)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = (64 * K ^ 5) * (r * (U + r * P ^ 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
    rw [HD.deriv]
    exact H.trans ((add_le_add H₁ H₂).trans_eq (by ring))
