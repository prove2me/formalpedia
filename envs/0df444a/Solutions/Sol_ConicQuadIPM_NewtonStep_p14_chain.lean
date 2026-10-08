-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.p14_chain
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:55:54.426448+00:00
-- url     : https://prove2.me/submissions/19006396-f305-4322-8bd8-df9b7e6f6238

import Definitions.Def_ConicQuadIPM_NewtonStep_Setting
import Theorems.Thm_ConicQuadIPM_NewtonStep_eq_61
import Theorems.Thm_ConicQuadIPM_NewtonStep_p14_first_eq

set_option autoImplicit false
open Matrix ConicQuadIPM.Complementarity ConicQuadIPM.NewtonStep

private theorem block_dim_pos {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (i : Fin k) : 0 < n i := by
  cases hkind : kind i with
  | nonneg => have h := (hwf i).1 hkind; omega
  | quad => exact (hwf i).2.1 hkind
  | rot => have h := (hwf i).2.2 hkind; omega

private theorem e1_dot_self {d : ℕ} (hd : 0 < d) :
    (e1 : Fin d → ℝ) ⬝ᵥ e1 = 1 := by
  classical
  unfold dotProduct
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [e1]
  · intro b _ hb
    have hb0 : b.val ≠ 0 := by
      intro he
      exact hb (Fin.ext he)
    simp [e1, hb0]
  · simp

theorem solution
    {m k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (A : (i : Fin k) → Matrix (Fin m) (Fin (n i)) ℝ) (b : Fin m → ℝ)
    (c : (i : Fin k) → Fin (n i) → ℝ)
    (x0 : (i : Fin k) → Fin (n i) → ℝ) (τ0 : ℝ) (y0 : Fin m → ℝ)
    (s0 : (i : Fin k) → Fin (n i) → ℝ) (κ0 : ℝ) (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1)
    (dx : (i : Fin k) → Fin (n i) → ℝ) (dτ : ℝ) (dy : Fin m → ℝ)
    (ds : (i : Fin k) → Fin (n i) → ℝ) (dκ : ℝ)
    (h22 : NewtonSystem kind n A b c x0 τ0 y0 s0 κ0 γ dx dτ dy ds dκ) :
    (∑ i, x0 i ⬝ᵥ ds i) + (∑ i, s0 i ⬝ᵥ dx i) + τ0 * dκ + κ0 * dτ
      = (γ - 1) * mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1)  := by
  rw [p14_first_eq kind n hwf x0 s0 dx ds τ0 κ0 dτ dκ]
  have hcomp := h22.2.2.2.1
  have he (i : Fin k) : (e1 : Fin (n i) → ℝ) ⬝ᵥ e1 = 1 :=
    e1_dot_self (block_dim_pos kind n hwf i)
  simp_rw [hcomp, dotProduct_add, dotProduct_neg, dotProduct_smul, smul_eq_mul]
  simp_rw [he, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib,
    (eq_61 kind n hwf x0 s0).1, (eq_61 kind n hwf x0 s0).2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmu : mu0 x0 τ0 s0 κ0 * ((k : ℝ) + 1) = (∑ i, x0 i ⬝ᵥ s0 i) + τ0 * κ0 := by
    unfold mu0
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith only [hmu, h22.2.2.2.2]

#print axioms solution
