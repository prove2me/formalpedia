-- Prove2me | solution 1 for FirstOrderOpt.FiniteSum.epoch_convergence_bound_v2
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:12:27.544534+00:00
-- url     : https://prove2.me/submissions/ad0a8cd8-3477-4488-aa69-298687e269fb

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

set_option autoImplicit false

section HelpersE82645F2
open MeasureTheory FirstOrderOpt.Prox

/-- `ω(x) = x²/2` on `[0,1]`, gradient `x ↦ (v ↦ x * v)`. -/
noncomputable def dgfE8 : DistanceGeneratingFunction (Set.Icc (0 : ℝ) 1) where
  ω := fun x => x ^ 2 / 2
  dω := fun x => x • (1 : ℝ →L[ℝ] ℝ)
  hasFDerivWithinAt := by
    intro x _
    have h : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      exact ((hasDerivAt_pow 2 x).div_const 2).congr_deriv (by norm_num)
    have heq : (x • (1 : ℝ →L[ℝ] ℝ)) = ContinuousLinearMap.toSpanSingleton ℝ x := by
      ext; simp
    show HasFDerivWithinAt (fun y : ℝ => y ^ 2 / 2) (x • (1 : ℝ →L[ℝ] ℝ)) _ x
    rw [heq]
    exact h.hasFDerivAt.hasFDerivWithinAt
  continuousOn_dω := by
    apply Continuous.continuousOn
    exact continuous_id.smul continuous_const
  strongConvex := by
    intro x _ y _
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
      Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (y - x)]

lemma dgfE8_V (a b : ℝ) : dgfE8.V a b = (b - a) ^ 2 / 2 := by
  simp only [DistanceGeneratingFunction.V, dgfE8, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

end HelpersE82645F2

open MeasureTheory FirstOrderOpt.Prox in
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (Ψ : E → ℝ) (hΨconv : ConvexOn ℝ X Ψ)
    (LQ γ : ℝ) (hLQ : 0 < LQ) (hγ : 0 < γ) (h4LQγ : 4 * LQ * γ ≤ 1)
    (T : ℕ → ℝ) (hT0pos : 0 < T 0) (hTpos : ∀ s, 1 ≤ s → 1 ≤ T s)
    (w : ℕ → ℝ)
    (hw : ∀ s, 1 ≤ s → w s = (1 - 4 * LQ * γ) * (T (s - 1) - 1) - 4 * LQ * γ * T s)
    (hwpos : ∀ s, 1 ≤ s → 0 < w s)
    (S : ℕ) (hS : 1 ≤ S)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, Ψ xstar ≤ Ψ y)
    (xtilde : ℕ → Ω → E) (hxtilde : ∀ s, 1 ≤ s → ∀ ω, xtilde s ω ∈ X)
    (x : ℕ → Ω → E) (hx : ∀ s, ∀ ω, x s ω ∈ X)
    (hx0eq : ∀ ω, x 0 ω = x0) (hxtilde0eq : ∀ ω, xtilde 0 ω = x0)
    (hintx : ∀ s, Integrable (fun ω => Ψ (x s ω)) μ)
    (hintxtilde : ∀ s, Integrable (fun ω => Ψ (xtilde s ω)) μ)
    (hintVxs : ∀ s, Integrable (fun ω => ν.V (x s ω) xstar) μ)
    (hepoch : ∀ s, 1 ≤ s →
      γ * (∫ ω, Ψ (x s ω) ∂μ - Ψ xstar) +
        (1 - 4 * LQ * γ) * γ * (T s - 1) * (∫ ω, Ψ (xtilde s ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x s ω) xstar ∂μ
      ≤ γ * (∫ ω, Ψ (x (s - 1) ω) ∂μ - Ψ xstar) +
        4 * LQ * γ ^ 2 * T s * (∫ ω, Ψ (xtilde (s - 1) ω) ∂μ - Ψ xstar) +
        ∫ ω, ν.V (x (s - 1) ω) xstar ∂μ)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω =
      (∑ s ∈ Finset.Icc 1 S, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 S, w s • xtilde s ω)
    (hint : Integrable (fun ω => Ψ (xbar ω)) μ),
    ∫ ω, Ψ (xbar ω) ∂μ - Ψ xstar ≤
      (γ * (1 + 4 * LQ * γ * T 1) * (Ψ x0 - Ψ xstar) + ν.V x0 xstar) /
        (γ * ∑ s ∈ Finset.Icc 1 S, w s)) := by
  intro H
  let T : ℕ → ℝ := fun s => if s = 0 then 101 else 2
  let w : ℕ → ℝ := fun s =>
    (1 - 4 * 1 * (1 / 16 : ℝ)) * (T (s - 1) - 1) - 4 * 1 * (1 / 16 : ℝ) * T s
  let xt : ℕ → Unit → ℝ := fun s _ => if s ≤ 1 then 1 else 0
  let xs : ℕ → Unit → ℝ := fun s _ => if s = 0 then 1 else 0
  have hw1 : w 1 = 149 / 2 := by simp [w, T]; norm_num
  have hwpos : ∀ s, 1 ≤ s → 0 < w s := by
    intro s hs
    rcases Nat.lt_or_ge s 2 with h | h
    · have : s = 1 := by omega
      subst this; rw [hw1]; norm_num
    · have h1 : s - 1 ≠ 0 := by omega
      have h2 : s ≠ 0 := by omega
      simp [w, T, h1, h2]; norm_num
  have hxt_mem : ∀ s, 1 ≤ s → ∀ ω, xt s ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro s _ ω; simp only [xt]; split_ifs <;> norm_num
  have hxs_mem : ∀ s, ∀ ω, xs s ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro s ω; simp only [xs]; split_ifs <;> norm_num
  have hepoch : ∀ s, 1 ≤ s →
      (1 / 16 : ℝ) * (∫ ω, (fun y : ℝ => y) (xs s ω) ∂(Measure.dirac ()) - (fun y : ℝ => y) 0) +
        (1 - 4 * 1 * (1 / 16 : ℝ)) * (1 / 16 : ℝ) * (T s - 1) *
          (∫ ω, (fun y : ℝ => y) (xt s ω) ∂(Measure.dirac ()) - (fun y : ℝ => y) 0) +
        ∫ ω, dgfE8.V (xs s ω) 0 ∂(Measure.dirac ())
      ≤ (1 / 16 : ℝ) * (∫ ω, (fun y : ℝ => y) (xs (s - 1) ω) ∂(Measure.dirac ()) - (fun y : ℝ => y) 0) +
        4 * 1 * (1 / 16 : ℝ) ^ 2 * T s *
          (∫ ω, (fun y : ℝ => y) (xt (s - 1) ω) ∂(Measure.dirac ()) - (fun y : ℝ => y) 0) +
        ∫ ω, dgfE8.V (xs (s - 1) ω) 0 ∂(Measure.dirac ()) := by
    intro s hs
    simp only [integral_dirac, dgfE8_V]
    rcases Nat.lt_or_ge s 3 with h | h
    · interval_cases s
      · norm_num [xs, xt, T]
      · norm_num [xs, xt, T]
    · have h1 : s - 1 ≠ 0 := by omega
      have h2 : s ≠ 0 := by omega
      have h3 : ¬ s ≤ 1 := by omega
      have h4 : ¬ s - 1 ≤ 1 := by omega
      simp [xs, xt, T, h1, h2, h3, h4]
  have key := @H ℝ _ _ Unit _ (Measure.dirac ()) _ (Set.Icc (0 : ℝ) 1) (convex_Icc 0 1)
    isClosed_Icc dgfE8 (fun y => y) (convexOn_id (convex_Icc 0 1)) 1 (1 / 16)
    (by norm_num) (by norm_num) (by norm_num) T (by simp [T]) (by
      intro s hs
      have h2 : s ≠ 0 := by omega
      simp [T, h2])
    w (fun s _ => rfl) hwpos 1 le_rfl 1 0 (by norm_num) (by norm_num)
    (fun y hy => hy.1) xt hxt_mem xs hxs_mem (fun _ => by simp [xs]) (fun _ => by simp [xt])
    (fun _ => Integrable.of_finite) (fun _ => Integrable.of_finite)
    (fun _ => Integrable.of_finite) hepoch
    (fun ω => (∑ s ∈ Finset.Icc 1 1, w s)⁻¹ • ∑ s ∈ Finset.Icc 1 1, w s • xt s ω)
    (fun _ => rfl) Integrable.of_finite
  simp only [integral_dirac, dgfE8_V, Finset.Icc_self, Finset.sum_singleton, hw1] at key
  simp [xt, T] at key
  norm_num at key
