-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_C1_resolvent_from_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:06:38.296433+00:00
-- url     : https://prove2.me/submissions/6a3210fe-f473-4113-a67d-4ab366c15df6

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_causal_signed_power_continuity_from_envelope
import Theorems.Thm_AvramDividend_Classical_causal_exp_scaled_primitive_continuous_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
import Theorems.Thm_AvramDividend_Classical_causal_neumann_C1_resolvent_of_signed_primitives
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A contracting Gaussian envelope gives a complete C1 Neumann resolvent. -/
theorem solution
    (k : ℝ → ℝ) (P F : ℕ → ℝ → ℝ) (a ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hkL1 : IntegrableOn k (Ioi (0 : ℝ)) volume)
    (hkcont : ContinuousOn k (Ioi (0 : ℝ)))
    (hkzero : ∀ x : ℝ, x ≤ 0 → k x = 0)
    (hP0 : P 0 = k)
    (hPrec : ∀ n : ℕ, P (n + 1) =
      fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, k s * P n (x - s) ∂volume)
    (hPL1 : ∀ n : ℕ, IntegrableOn (P n) (Ioi (0 : ℝ)) volume)
    (hFL1 : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hDom : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → |P n x| ≤ F n x)
    (hFmass : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      (∫ s in Ioc (0 : ℝ) x, F n s ∂volume) ≤ ρ ^ (n + 1))
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∃ g : ℝ → ℝ,
      (g = fun y : ℝ => 1 / a + Real.exp (w * y) *
        (∑' n : ℕ, (Real.exp (-w * y) *
          (∫ s in Ioc (0 : ℝ) y,
            Real.exp (w * s) * P n s ∂volume)) / a)) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) := by
  let H : ℕ → ℝ → ℝ := fun n x =>
    (Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P n s ∂volume)) / a
  have hPcont := causal_signed_power_continuity_from_envelope
    k P F ρ hρ0 hkL1 hkcont hkzero hP0 hPrec hPL1 hDom hFpoint
  have hPbound : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x := by
    intro ε hε n x hx
    exact (hDom n x (le_of_lt (lt_of_lt_of_le hε hx))).trans
      (hFpoint n x (lt_of_lt_of_le hε hx))
  have hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)) := by
    intro n
    exact causal_exp_scaled_primitive_continuous_nonnegative
      (P n) a w hw (hPL1 n)
  have hHbound : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a := by
    intro n x hx
    rcases eq_or_lt_of_le hx with hzero | hxpos
    · subst x
      have hr : 0 ≤ ρ ^ (n + 1) / a :=
        div_nonneg (pow_nonneg hρ0 _) ha.le
      simpa [H] using hr
    · exact causal_scaled_primitive_mass_bound
        (P n) (F n) a w x (ρ ^ (n + 1)) ha hw hxpos
        (hPL1 n) (hFL1 n) (hDom n) (hFmass n x hx)
  have hHdef : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P n s ∂volume)) / a := by
    intro n
    rfl
  obtain ⟨g, hg, hgcont, hgc1⟩ :=
    causal_neumann_C1_resolvent_of_signed_primitives
      P H a ρ w ha hρ0 hρ1 hw hPbound hHbound hHcont hHdef hPL1 hPcont
  refine ⟨g, ?_, hgcont, hgc1⟩
  simpa only [H] using hg
