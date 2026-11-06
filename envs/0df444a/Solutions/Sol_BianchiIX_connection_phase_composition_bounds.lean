-- Prove2me | solution 1 for BianchiIX.connection_phase_composition_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:52:00.286587+00:00
-- url     : https://prove2.me/submissions/5128d904-4cc3-453d-9fc9-61971988023f

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


/-- Combining the core and connection errors preserves the amplitude weights before taking reciprocals. -/
theorem solution {f k Δ g : ℝ → ℝ} {x r U W C₀ C₁ C : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hU : 0 ≤ U) (hW : 0 ≤ W ∧ W ≤ 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC : 0 ≤ C)
    (hf : DifferentiableAt ℝ f x) (hk : DifferentiableAt ℝ k x) (hΔ : DifferentiableAt ℝ Δ x)
    (hg : g =ᶠ[𝓝 x] fun a => f a - 2 + Δ a)
    (hfv : |f x - k x| ≤ C₀ * (U + r * W ^ 2))
    (hfd : |deriv (fun a => f a - k a) x| ≤ C₁ * (U + r * W) / r ^ 2)
    (hΔv : |Δ x| ≤ C * r * (U + W ^ 2)) (hΔd : |deriv Δ x| ≤ C * (U + W ^ 2)) :
    DifferentiableAt ℝ g x ∧
      |g x - (k x - 2)| ≤ (C₀ + C₁ + C) * (U + r * W ^ 2) ∧
      |deriv g x - deriv k x| ≤ (C₀ + C₁ + C) * (U + r * W) / r ^ 2 := by
  have hr0 := hr.1
  have hW0 := hW.1
  have Hg : HasDerivAt g (deriv f x + deriv Δ x) x :=
    ((hf.hasDerivAt.sub_const 2).add hΔ.hasDerivAt).congr_of_eventuallyEq hg
  have hRU : r * U ≤ U := mul_le_of_le_one_left hU hr.2
  refine ⟨Hg.differentiableAt, ?_, ?_⟩
  · have heq : g x - (k x - 2) = (f x - k x) + Δ x := by rw [hg.self_of_nhds]; ring
    rw [heq]
    have HΔv : |Δ x| ≤ C * (U + r * W ^ 2) := hΔv.trans (by
      have H := mul_le_mul_of_nonneg_left hRU hC
      nlinarith only [H])
    have Htotal := (abs_add_le (f x - k x) (Δ x)).trans (add_le_add hfv HΔv)
    have Hextra : 0 ≤ C₁ * (U + r * W ^ 2) := by positivity
    nlinarith only [Htotal, Hextra]
  · have hRW : 0 ≤ r * W ∧ r * W ≤ 1 :=
      ⟨mul_nonneg hr.1.le hW.1, (mul_le_mul hr.2 hW.2 hW.1 (by norm_num)).trans_eq (by ring)⟩
    have hsmall : r ^ 2 * (U + W ^ 2) ≤ U + r * W := by
      have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr.1, hr.2]
      nlinarith only [mul_le_mul_of_nonneg_right hr2 hU,
        mul_le_mul_of_nonneg_right hRW.2 hRW.1]
    have HΔd : |deriv Δ x| ≤ C * (U + r * W) / r ^ 2 := hΔd.trans (by
      apply (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr
      have H := mul_le_mul_of_nonneg_left hsmall hC
      nlinarith only [H])
    have Hf := hfd
    rw [deriv_fun_sub hf hk] at Hf
    rw [Hg.deriv]
    have Htotal := (abs_add_le (deriv f x - deriv k x) (deriv Δ x)).trans (add_le_add Hf HΔd)
    have Hextra : 0 ≤ C₀ * (U + r * W) / r ^ 2 := by positivity
    calc
      _ = |(deriv f x - deriv k x) + deriv Δ x| := by congr 1; ring
      _ ≤ C₁ * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2 := Htotal
      _ ≤ C₀ * (U + r * W) / r ^ 2 +
          (C₁ * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2) := le_add_of_nonneg_left Hextra
      _ = _ := by ring
