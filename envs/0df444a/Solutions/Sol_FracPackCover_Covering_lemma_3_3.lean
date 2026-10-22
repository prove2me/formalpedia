-- Prove2me | solution 1 for FracPackCover.Covering.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:04:22.262309+00:00
-- url     : https://prove2.me/submissions/9cef9e9f-525b-4c37-8153-55e89ffc9335

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic

set_option autoImplicit false
open FracPackCover.Covering

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (x xt : Fin n → ℝ) (hx : x ∈ P) (hxt : xt ∈ P)
    (ε α σ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ ε / (4 * α * ρ))
    (hmax : ∀ x' ∈ P, yAx A (dualY A b α x) x' ≤ yAx A (dualY A b α x) xt)
    (hC2 : ¬ C2 A b ε (dualY A b α x) x (yAx A (dualY A b α x) xt)) :
    ε * α * σ * potential A b α x ≤
      potential A b α x - potential A b α ((1 - σ) • x + σ • xt) := by
  obtain ⟨hA, hb, hconv, hne, hnn⟩ := hdata
  obtain ⟨hρpos, hwid⟩ := hρ
  have hrow : ∀ x' ∈ P, ∀ i, 0 ≤ rowVal A x' i := fun x' hx' i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hnn x' hx' j)
  set w : Fin m → ℝ := fun i => Real.exp (-(α * rowVal A x i / b i)) with hw
  have hwpos : ∀ i, 0 < w i := fun i => Real.exp_pos _
  have hytb : ytb b (dualY A b α x) = ∑ i, w i := by
    unfold ytb dualY
    apply Finset.sum_congr rfl
    intro i _
    have := (hb i).ne'
    simp only [hw]
    field_simp
  have hpot : potential A b α x = ∑ i, w i := hytb
  have hlin : ∀ i, rowVal A ((1 - σ) • x + σ • xt) i
      = (1 - σ) * rowVal A x i + σ * rowVal A xt i := by
    intro i
    simp only [rowVal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  set δ : Fin m → ℝ := fun i => α * σ * (rowVal A xt i - rowVal A x i) / b i with hδ
  have hwhat : potential A b α ((1 - σ) • x + σ • xt) = ∑ i, w i * Real.exp (-δ i) := by
    show ytb b (dualY A b α ((1 - σ) • x + σ • xt)) = _
    unfold ytb dualY
    apply Finset.sum_congr rfl
    intro i _
    have := (hb i).ne'
    rw [hlin i]
    simp only [hw, hδ]
    rw [← Real.exp_add]
    have : (1 / b i) * Real.exp (-(α * ((1 - σ) * rowVal A x i + σ * rowVal A xt i) / b i)) * b i
        = Real.exp (-(α * ((1 - σ) * rowVal A x i + σ * rowVal A xt i) / b i)) := by
      field_simp
    rw [this]
    congr 1
    field_simp
    ring
  -- bounds
  have hασρ : α * σ * ρ ≤ ε / 4 := by
    have h1 : σ * (4 * α * ρ) ≤ ε := by
      have := (le_div_iff₀ (by positivity : 0 < 4 * α * ρ)).1 hσ
      exact this
    nlinarith
  have hδabs : ∀ i, |δ i| ≤ ε / 4 := by
    intro i
    have hbi := hb i
    have h1 := hrow xt hxt i
    have h2 := hrow x hx i
    have h3 : rowVal A xt i ≤ ρ * b i := hwid xt hxt i
    have h4 : rowVal A x i ≤ ρ * b i := hwid x hx i
    simp only [hδ]
    rw [abs_div, abs_of_pos hbi, div_le_iff₀ hbi, abs_mul, abs_of_nonneg (by positivity : 0 ≤ α * σ)]
    have : |rowVal A xt i - rowVal A x i| ≤ ρ * b i := by
      rw [abs_le]; constructor <;> linarith
    calc α * σ * |rowVal A xt i - rowVal A x i| ≤ α * σ * (ρ * b i) := by gcongr
      _ = (α * σ * ρ) * b i := by ring
      _ ≤ ε / 4 * b i := by gcongr
  have hexp : ∀ i, Real.exp (-δ i) ≤ 1 - δ i + δ i ^ 2 := by
    intro i
    have h := Real.abs_exp_sub_one_sub_id_le (x := -δ i) (by rw [abs_neg]; linarith [hδabs i])
    have := (abs_le.1 h).2
    nlinarith
  -- sums
  set C := yAx A (dualY A b α x) xt with hC
  set Y := yAx A (dualY A b α x) x with hY
  have hYle : Y ≤ C := hmax x hx
  have hyx : ∀ x' : Fin n → ℝ, yAx A (dualY A b α x) x' = ∑ i, w i * rowVal A x' i / b i := by
    intro x'
    unfold yAx dualY
    apply Finset.sum_congr rfl
    intro i _
    simp only [hw]
    ring
  have hC0 : 0 ≤ C := by
    rw [hC, hyx]
    exact Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hwpos i).le (hrow xt hxt i)) (hb i).le
  have hS1 : ∑ i, w i * δ i = α * σ * (C - Y) := by
    rw [hC, hY, hyx, hyx, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hδ]
    ring
  have hS2 : ∑ i, w i * δ i ^ 2 ≤ ε / 4 * (α * σ * (C + Y)) := by
    rw [hC, hY, hyx, hyx, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hbi := hb i
    have h1 := hrow xt hxt i
    have h2 := hrow x hx i
    have hwi := hwpos i
    have habs : |δ i| ≤ ε / 4 := hδabs i
    have hd2 : δ i ^ 2 ≤ ε / 4 * |δ i| := by
      rw [← sq_abs]; nlinarith [abs_nonneg (δ i)]
    have hd3 : |δ i| ≤ α * σ * (rowVal A xt i + rowVal A x i) / b i := by
      simp only [hδ]
      rw [abs_div, abs_of_pos hbi]
      apply div_le_div_of_nonneg_right _ hbi.le
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ α * σ)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [abs_le]; constructor <;> linarith
    calc w i * δ i ^ 2 ≤ w i * (ε / 4 * |δ i|) := by gcongr
      _ ≤ w i * (ε / 4 * (α * σ * (rowVal A xt i + rowVal A x i) / b i)) := by gcongr
      _ = ε / 4 * (α * σ * (w i * rowVal A xt i / b i + w i * rowVal A x i / b i)) := by
          field_simp
  -- assemble
  have hC2' : ε * (C + ∑ i, w i) < C - Y := by
    unfold C2 at hC2
    rw [hytb] at hC2
    push Not at hC2
    exact hC2
  have hΦ : ∑ i, w i - ∑ i, w i * Real.exp (-δ i) ≥ α * σ * (C - Y) - ε / 4 * (α * σ * (C + Y)) := by
    have : ∑ i, w i * Real.exp (-δ i) ≤ ∑ i, (w i - w i * δ i + w i * δ i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have := hexp i
      have := hwpos i
      nlinarith
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hS1] at this
    nlinarith [hS2]
  rw [hpot, hwhat]
  have hΦpos : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hwpos i).le
  have hασ : 0 ≤ α * σ := by positivity
  have hmain : ε * ∑ i, w i ≤ (C - Y) - ε / 4 * (C + Y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hmain hασ]
