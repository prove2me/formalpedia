-- Prove2me | solution 1 for AzumaWeightedSums.StrongLaw.remark1_condMGF_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:23:35.740684+00:00
-- url     : https://prove2.me/submissions/e20e99c9-6f90-4e2f-9560-169163cb23f1

import Mathlib
import Definitions.Def_AzumaWeightedSums_IteratedLog_ClassG

namespace Azuma2c67ace7

lemma exp_le_cosh_add (t K y : ℝ) (hy : |y| ≤ K) :
    Real.exp (t * y) ≤ Real.cosh (t * K) + y * (Real.sinh (t * K) / K) := by
  rcases eq_or_lt_of_le ((abs_nonneg y).trans hy) with hK | hK
  · subst hK
    have : y = 0 := abs_nonpos_iff.mp hy
    subst this
    simp
  · have h1 : -K ≤ y := (abs_le.mp hy).1
    have h2 : y ≤ K := (abs_le.mp hy).2
    have ha : 0 ≤ (1 - y / K) / 2 := by
      have : y / K ≤ 1 := (div_le_one hK).mpr h2
      linarith
    have hb : 0 ≤ (1 + y / K) / 2 := by
      have : -1 ≤ y / K := by
        rw [le_div_iff₀ hK]; linarith
      linarith
    have hab : (1 - y / K) / 2 + (1 + y / K) / 2 = 1 := by ring
    have hc := convexOn_exp.2 (Set.mem_univ (-(t * K))) (Set.mem_univ (t * K)) ha hb hab
    simp only [smul_eq_mul] at hc
    have e1 : (1 - y / K) / 2 * -(t * K) + (1 + y / K) / 2 * (t * K) = t * y := by
      field_simp
      ring
    rw [e1] at hc
    rw [Real.cosh_eq, Real.sinh_eq]
    have e2 : (1 - y / K) / 2 * Real.exp (-(t * K)) + (1 + y / K) / 2 * Real.exp (t * K)
        = (Real.exp (t * K) + Real.exp (-(t * K))) / 2
          + y * ((Real.exp (t * K) - Real.exp (-(t * K))) / 2 / K) := by
      field_simp
      ring
    linarith [hc, e2.le, e2.ge]

end Azuma2c67ace7

open MeasureTheory in
theorem solution {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) (x : ℕ → Ω → ℝ)
    (hx : AzumaWeightedSums.IteratedLog.IsMartingaleDiff μ ℱ x) (K : ℕ → ℝ)
    (hK : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂μ, |x n ω| ≤ K n) :
    ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      (μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)]
          ≤ᵐ[μ] fun _ => Real.cosh (t * K n)) ∧
      (μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)]
          ≤ᵐ[μ] fun _ => Real.exp (t ^ 2 * K n ^ 2 / 2)) := by
  intro n hn t
  obtain ⟨hsm, hint, hce⟩ := hx n hn
  have hKn := hK n hn
  set c : ℝ := Real.sinh (t * K n) / K n with hc
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (t * x n ω)) μ := by
    have : AEStronglyMeasurable (x n) μ := (hsm.mono (ℱ.le n)).aestronglyMeasurable
    exact Real.continuous_exp.comp_aestronglyMeasurable (this.const_mul t)
  have hpt : (fun ω => Real.exp (t * x n ω)) ≤ᵐ[μ]
      (fun ω => Real.cosh (t * K n) + c * x n ω) := by
    filter_upwards [hKn] with ω hω
    have := Azuma2c67ace7.exp_le_cosh_add t (K n) (x n ω) hω
    rw [hc]; linarith
  have hint2 : Integrable (fun ω => Real.cosh (t * K n) + c * x n ω) μ :=
    (integrable_const _).add (hint.const_mul c)
  have hint1 : Integrable (fun ω => Real.exp (t * x n ω)) μ := by
    refine Integrable.mono' hint2.abs hmeas ?_
    filter_upwards [hpt] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hω.trans (le_abs_self _)
  have hmono := condExp_mono (m := ℱ (n - 1)) hint1 hint2 hpt
  have hadd : μ[fun ω => Real.cosh (t * K n) + c * x n ω | ℱ (n - 1)] =ᵐ[μ]
      fun _ => Real.cosh (t * K n) := by
    have e : (fun ω => Real.cosh (t * K n) + c * x n ω)
        = (fun _ => Real.cosh (t * K n)) + c • x n := by
      funext ω; simp [smul_eq_mul]
    rw [e]
    have h1 := condExp_add (m := ℱ (n - 1)) (integrable_const (μ := μ) (Real.cosh (t * K n)))
      (hint.smul c)
    have h2 : μ[c • x n | ℱ (n - 1)] =ᵐ[μ] c • μ[x n | ℱ (n - 1)] := condExp_smul c (x n) _
    rw [condExp_const (ℱ.le (n - 1))] at h1
    filter_upwards [h1, h2, hce] with ω e1 e2 e3
    rw [e1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e2 ⊢
    rw [e2, e3]; simp
  have hA : μ[fun ω => Real.exp (t * x n ω) | ℱ (n - 1)] ≤ᵐ[μ]
      fun _ => Real.cosh (t * K n) := by
    filter_upwards [hmono, hadd] with ω a b
    rw [← b]; exact a
  refine ⟨hA, ?_⟩
  filter_upwards [hA] with ω a
  refine a.trans ?_
  have := Real.cosh_le_exp_half_sq (t * K n)
  calc Real.cosh (t * K n) ≤ Real.exp ((t * K n) ^ 2 / 2) := this
    _ = Real.exp (t ^ 2 * K n ^ 2 / 2) := by ring_nf
