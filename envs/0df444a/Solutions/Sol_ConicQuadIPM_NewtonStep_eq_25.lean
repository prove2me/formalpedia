-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:49:33.415721+00:00
-- url     : https://prove2.me/submissions/9eebdad0-6bcd-44ad-8034-f5a3d4efddbe

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

open Matrix ConicQuadIPM.NewtonStep

theorem solution
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, A i *ᵥ ((1 - γ) • x0 i + dx i)) - ((1 - γ) * τ0 + dτ) • b = 0 ∧
    (∀ i, (A i)ᵀ *ᵥ ((1 - γ) • y0 + dy) + ((1 - γ) • s0 i + ds i)
        - ((1 - γ) * τ0 + dτ) • c i = 0) ∧
    -(∑ i, c i ⬝ᵥ ((1 - γ) • x0 i + dx i)) + b ⬝ᵥ ((1 - γ) • y0 + dy)
        - ((1 - γ) * κ0 + dκ) = 0 := by
  rcases h22 with ⟨hprimal, hdual, hgap, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [mulVec_add, mulVec_smul]
    ext j
    have hj := congrFun hprimal j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      Finset.sum_apply] at hj ⊢
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hj]
  · intro i
    simp only [mulVec_add, mulVec_smul]
    ext j
    have hj := congrFun (hdual i) j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hj ⊢
    nlinarith [hj]
  · simp only [dotProduct_add, dotProduct_smul, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hgap]

#print axioms solution
