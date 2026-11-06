-- Prove2me | solution 1 for BianchiIX.connection_reciprocal_radial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:27:36.057121+00:00
-- url     : https://prove2.me/submissions/965435e7-d5ec-4890-92db-728997942fc7

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
open Filter
open scoped Topology

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

section
noncomputable section
open BianchiIX

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

end
end


/-- The combined radial error gives the value and ordinary derivative bounds of E.28. -/
theorem solution {g k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hg : DifferentiableAt ℝ g x) (hk : DifferentiableAt ℝ k x)
    (hk6 : 6 ≤ k x) (hklo : 2 / (K * r) ≤ k x) (hglo : k x / 4 ≤ g x)
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (he : |g x - (k x - 2)| ≤ C * (U + r * P ^ 2))
    (hde : |deriv g x - deriv k x| ≤ C * (U + r * P) / r ^ 2) :
    let E := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
    DifferentiableAt ℝ E x ∧ |E x| ≤ 8 * C * K ^ 2 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv E x| ≤ (8 * C * K ^ 2 + 32 * C * K ^ 4) * (U + r * P) := by
  intro E
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hP0 := hP.1
  have hα : 0 < 2 * K * r := by positivity
  have hfloor : 1 / (2 * K * r) ≤ k x / 4 := by
    calc
      _ = (2 / (K * r)) / 4 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hklo (by norm_num)
  have hgf := hfloor.trans hglo
  have hkf : 1 / (2 * K * r) ≤ k x - 2 := hfloor.trans (by linarith only [hk6])
  have hg0 : 0 < g x := (one_div_pos.mpr hα).trans_le hgf
  have hk0 : 0 < k x - 2 := by linarith only [hk6]
  have Hk : HasDerivAt (fun a => k a - 2) (deriv k x) x := hk.hasDerivAt.sub_const 2
  have HD := hasDerivAt_reciprocal_error hg.hasDerivAt Hk hg0.ne' hk0.ne'
  have Hval : |2 / g x - 2 / (k x - 2)| ≤ 8 * C * K ^ 2 * r ^ 2 * (U + r * P ^ 2) :=
    (reciprocal_difference_value_bound hα hgf hkf).trans
    ((mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * (2 * K * r) ^ 2)).trans_eq (by ring))
  have hq : |deriv k x| ≤ (4 * K ^ 3) / (2 * K * r) ^ 2 := hdk.trans_eq (by field_simp; norm_num)
  have Hb := reciprocal_difference_derivative_bound hα hgf hkf hq
    (Θ := g x - (k x - 2)) (p := deriv g x - deriv k x)
  have H1 : 2 * (2 * K * r) ^ 2 * |deriv g x - deriv k x| ≤
      8 * C * K ^ 2 * (U + r * P) :=
    (mul_le_mul_of_nonneg_left hde (by positivity)).trans_eq (by field_simp; ring)
  have hPr : 0 ≤ r * P ∧ r * P ≤ 1 :=
    ⟨mul_nonneg hr.1.le hP.1, (mul_le_mul hr.2 hP.2 hP.1 (by norm_num)).trans_eq (by ring)⟩
  have hsmall : r * (U + r * P ^ 2) ≤ U + r * P := by
    nlinarith only [mul_le_mul_of_nonneg_right hr.2 hU,
      mul_le_mul_of_nonneg_right hPr.2 hPr.1]
  have H2 : 4 * (4 * K ^ 3) * (2 * K * r) * |g x - (k x - 2)| ≤
      32 * C * K ^ 4 * (U + r * P) := by
    calc
      _ ≤ 4 * (4 * K ^ 3) * (2 * K * r) * (C * (U + r * P ^ 2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (32 * C * K ^ 4) * (r * (U + r * P ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have HM : E =ᶠ[𝓝 x] (fun a => 2 / g a - 2 / (k a - 2)) := by
    filter_upwards [hk.continuousAt.eventually (lt_mem_nhds (show 2 < k x by linarith only [hk6]))] with a ha
    have hka : k a ≠ 0 := ne_of_gt (by linarith only [ha])
    have hka2 : k a - 2 ≠ 0 := ne_of_gt (by linarith only [ha])
    dsimp only [E]
    congr 1
    field_simp
  refine ⟨HD.differentiableAt.congr_of_eventuallyEq HM, ?_, ?_⟩
  · rw [HM.self_of_nhds]
    exact Hval
  · rw [HM.deriv_eq, HD.deriv]
    exact Hb.trans ((add_le_add H1 H2).trans_eq (by ring))
