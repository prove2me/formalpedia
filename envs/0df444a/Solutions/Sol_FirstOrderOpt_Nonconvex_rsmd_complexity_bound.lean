-- Prove2me | solution 1 for FirstOrderOpt.Nonconvex.rsmd_complexity_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-27T23:21:13.301599+00:00
-- url     : https://prove2.me/submissions/cf5ca9ae-d9fc-4a11-9da9-c658e0b69c19

import Mathlib

open scoped RealInnerProductSpace
open MeasureTheory

/-- Counterexample: nothing constrains `V` (the book's Bregman distance). With `V = 0`,
`f = h = 0`, `fGrad = 0` and exact gradients `G = 0` (so `σ = 0`), every point is a generalized
projection, so the deterministic iterates `x k = k - 1`, `xPlus k = k` in `E = ℝ` are
admissible on the one-point probability space. With `L = 1`, `N = 1`, `γ = 1/2`, `m = 1` and
`R ≡ 1`, we get `Ψ* = 0`, `DΨ = 0`, and `E‖g̃_R‖² = ‖2 • (0 - 1)‖² = 4`, while the claimed
bound is `(L·0 + 0) / (1/2 - 1/4) = 0`. -/
theorem solution : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : Type} {m0 : MeasurableSpace Ω} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] (𝒢 : MeasureTheory.Filtration ℕ m0)
    (X : Set E) (f h : E → ℝ) (V : E → E → ℝ) (L σ : ℝ) (hL : 0 < L) (hσ : 0 ≤ σ)
    (fGrad : E → E)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - ⟪fGrad x, y - x⟫ ≤ (L / 2) * ‖y - x‖ ^ 2)
    (N : ℕ) (hN : 1 ≤ N)
    (x1 : E) (hx1 : x1 ∈ X)
    (x G xPlus gXtilde : ℕ → Ω → E) (γ mBatch : ℕ → ℝ)
    (hmBatch : ∀ k, 1 ≤ k → k ≤ N → 0 < mBatch k)
    (hx1def : ∀ ω, x 1 ω = x1)
    (hxMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (x k))
    (hGMeas : ∀ k, 1 ≤ k → StronglyMeasurable[𝒢 (k - 1)] (G k))
    (hx : ∀ k, ∀ ω, x k ω ∈ X) (hxPlusMem : ∀ k, ∀ ω, xPlus k ω ∈ X)
    (hxPlusDef : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, ∀ u ∈ X,
      ⟪G k ω, xPlus k ω⟫ + (1 / γ k) * V (x k ω) (xPlus k ω) + h (xPlus k ω) ≤
        ⟪G k ω, u⟫ + (1 / γ k) * V (x k ω) u + h u)
    (hxNext : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, x (k + 1) ω = xPlus k ω)
    (hgXtilde : ∀ k, 1 ≤ k → k ≤ N → ∀ ω, gXtilde k ω = (1 / γ k) • (x k ω - xPlus k ω))
    (hγpos : ∀ k, 1 ≤ k → k ≤ N → 0 < γ k) (hγub : ∀ k, 1 ≤ k → k ≤ N → γ k ≤ 1 / L)
    (hγstrict : ∃ k, 1 ≤ k ∧ k ≤ N ∧ γ k < 1 / L)
    (hDeltaInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => G k ω - fGrad (x k ω)) P)
    (hDeltaSqInt : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.Integrable (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) P)
    (hUnbiased : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => G k ω - fGrad (x k ω)) =ᵐ[P] 0)
    (hVariance : ∀ k, 1 ≤ k → k ≤ N →
      MeasureTheory.condExp (𝒢 (k - 1)) P (fun ω => ‖G k ω - fGrad (x k ω)‖ ^ 2) ≤ᵐ[P]
        (fun _ => σ ^ 2 / mBatch k))
    (ΨStar : ℝ) (hΨStar : IsGLB ((fun x => f x + h x) '' X) ΨStar)
    (DΨ : ℝ) (hDΨ : DΨ = Real.sqrt ((f x1 + h x1 - ΨStar) / L))
    (R : Ω → ℕ) (hRmeas : Measurable R) (hRsupp : ∀ ω, 1 ≤ R ω ∧ R ω ≤ N)
    (PR : ℕ → ℝ)
    (hPR : ∀ k, 1 ≤ k → k ≤ N →
      PR k = (γ k - L * (γ k) ^ 2) / ∑ j ∈ Finset.Icc 1 N, (γ j - L * (γ j) ^ 2))
    (hRlaw : ∀ k, 1 ≤ k → k ≤ N → P {ω | R ω = k} = ENNReal.ofReal (PR k))
    (hRindep : ∀ k, 1 ≤ k → k ≤ N → ProbabilityTheory.IndepFun R (gXtilde k) P)
    (gXtildeR : Ω → E) (hgXtildeR : ∀ ω, gXtildeR ω = gXtilde (R ω) ω)
    (hgXtildeRInt : MeasureTheory.Integrable (fun ω => ‖gXtildeR ω‖ ^ 2) P),
    ∫ ω, ‖gXtildeR ω‖ ^ 2 ∂P ≤
      (L * DΨ ^ 2 + σ ^ 2 * ∑ k ∈ Finset.Icc 1 N, (γ k / mBatch k)) /
        ∑ k ∈ Finset.Icc 1 N, (γ k - L * (γ k) ^ 2)) := by
  intro H
  have hglb : IsGLB ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) 0 := by
    have e : ((fun x : ℝ => (0 : ℝ) + 0) '' Set.univ) = {0} := by ext; simp
    rw [e]; exact isGLB_singleton
  let 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace Unit) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Unit) le_rfl
  have := H (E := ℝ) (Ω := Unit) (Measure.dirac ()) 𝒢 Set.univ (fun _ => 0) (fun _ => 0)
    (fun _ _ => 0) 1 0 one_pos le_rfl (fun _ => 0) (fun x _ y _ => by simp; positivity) 1 le_rfl 0 trivial
    (fun k _ => (k : ℝ) - 1) (fun _ _ => 0) (fun k _ => (k : ℝ))
    (fun k _ => (1 / (1 / 2 : ℝ)) • (((k : ℝ) - 1) - (k : ℝ))) (fun _ => 1 / 2) (fun _ => 1)
    (fun _ _ _ => one_pos) (fun _ => by simp) (fun _ _ => stronglyMeasurable_const)
    (fun _ _ => stronglyMeasurable_const) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun k _ _ _ u _ => by simp) (fun k _ _ _ => by push_cast; ring) (fun _ _ _ _ => rfl)
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) ⟨1, le_rfl, le_rfl, by norm_num⟩
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp; rfl)
    (fun _ _ _ => by simp; exact Filter.Eventually.of_forall (fun _ => le_rfl))
    0 hglb 0 (by simp) (fun _ => 1) measurable_const (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun _ => ((1 / 2 : ℝ) - 1 * (1 / 2) ^ 2) /
      ∑ j ∈ Finset.Icc 1 1, ((1 / 2 : ℝ) - 1 * (1 / 2) ^ 2))
    (fun _ _ _ => rfl)
    (fun k hk1 hk2 => by
      obtain rfl : k = 1 := by omega
      norm_num)
    (fun _ _ _ => ProbabilityTheory.indepFun_const_left _ _)
    (fun ω => (1 / (1 / 2 : ℝ)) • ((((1 : ℕ) : ℝ) - 1) - ((1 : ℕ) : ℝ))) (fun _ => rfl)
    (by simp)
  norm_num at this
