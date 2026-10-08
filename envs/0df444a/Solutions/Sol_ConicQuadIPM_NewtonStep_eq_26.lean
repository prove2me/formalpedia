-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.eq_26
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:52:18.954417+00:00
-- url     : https://prove2.me/submissions/879d555d-bf1a-4aea-8d93-a8801d5ad83e

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting
import Theorems.Thm_ConicQuadIPM_NewtonStep_eq_25

open Matrix ConicQuadIPM.NewtonStep

private lemma homogeneous_gap {m k : ℕ} {n : Fin k → ℕ}
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c x s : (i : Fin k) → Fin (n i) → ℝ) (y : Fin m → ℝ) (τ κ : ℝ)
    (hp : (∑ i, A i *ᵥ x i) - τ • b = 0)
    (hd : ∀ i, (A i)ᵀ *ᵥ y + s i - τ • c i = 0)
    (hg : -(∑ i, c i ⬝ᵥ x i) + b ⬝ᵥ y - κ = 0) :
    0 = (∑ i, x i ⬝ᵥ s i) + τ * κ := by
  have hblock : ∀ i, x i ⬝ᵥ s i =
      τ * (c i ⬝ᵥ x i) - y ⬝ᵥ (A i *ᵥ x i) := by
    intro i
    have hi := congrArg (fun v => x i ⬝ᵥ v) (hd i)
    simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_zero, dotProduct_transpose_mulVec, dotProduct_comm (x i) (c i)] at hi
    linarith
  have hpr := congrArg (fun v => y ⬝ᵥ v) hp
  simp only [dotProduct_sub, dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_zero, dotProduct_comm y b] at hpr
  simp_rw [hblock]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hgm := congrArg (fun z : ℝ => τ * z) hg
  nlinarith [hpr, hgm]
theorem solution
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    0 = (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ) ∧
    (∑ i, ((1 - γ) • x0 i + dx i) ⬝ᵥ ((1 - γ) • s0 i + ds i))
          + ((1 - γ) * τ0 + dτ) * ((1 - γ) * κ0 + dκ)
      = (1 - γ) ^ 2 * ((∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0)
        + (1 - γ) * ((∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ)
        + ((∑ i, dx i ⬝ᵥ ds i) + dτ * dκ) := by
  obtain ⟨hp, hd, hg⟩ := ConicQuadIPM.NewtonStep.eq_25 kind n hwf A b c x0 τ0 y0 s0 κ0 γ hγ dx dτ dy ds dκ h22
  constructor
  · exact homogeneous_gap A b c (fun i => (1 - γ) • x0 i + dx i)
      (fun i => (1 - γ) • s0 i + ds i) ((1 - γ) • y0 + dy)
      ((1 - γ) * τ0 + dτ) ((1 - γ) * κ0 + dκ) hp hd hg
  · simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm (dx _) (s0 _), Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

#print axioms solution