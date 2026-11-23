-- Prove2me | solution 1 for EquivarianceConvolution.gcnn_is_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T21:11:37.157099+00:00
-- url     : https://prove2.me/submissions/489ef7ce-656c-4b54-a110-fb6ba3e4bc14

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators
namespace EquivarianceConvolution


theorem gcnn_is_equivariant {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) (hN : IsGCNN H L N) :
    IsEquivariantNet G L N := by
  have hconv : ∀ l < L, ∀ (g : G) (f : G ⧸ H l → Fin (d l) → ℂ),
      N.phi l (translateFun g f) = translateFun g (N.phi l f) := by
    intro l hl g f
    obtain ⟨χ, -, hχ⟩ := hN l hl
    funext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      have e1 := hχ (translateFun g f) u
      have e2 := hχ f (g⁻¹ * u)
      simp only [liftQ] at e1 e2
      simp only [translateFun, MulAction.Quotient.smul_mk, smul_eq_mul]
      rw [e1, e2]
      unfold vecConv
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [liftQ, translateFun, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]
  intro g f₀ l hl
  induction l with
  | zero => rfl
  | succ l ih =>
    funext x
    simp only [FeedForwardNet.act]
    rw [ih (by omega), hconv l (by omega)]
    rfl


end EquivarianceConvolution

open EquivarianceConvolution in
theorem solution {G : Type*} [Group G] [Fintype G] (H : ℕ → Subgroup G)
    {d : ℕ → ℕ} (L : ℕ) (N : FeedForwardNet (fun l => G ⧸ H l) d) (hN : IsGCNN H L N) :
    IsEquivariantNet G L N := by
  have hconv : ∀ l < L, ∀ (g : G) (f : G ⧸ H l → Fin (d l) → ℂ),
      N.phi l (translateFun g f) = translateFun g (N.phi l f) := by
    intro l hl g f
    obtain ⟨χ, -, hχ⟩ := hN l hl
    funext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      have e1 := hχ (translateFun g f) u
      have e2 := hχ f (g⁻¹ * u)
      simp only [liftQ] at e1 e2
      simp only [translateFun, MulAction.Quotient.smul_mk, smul_eq_mul]
      rw [e1, e2]
      unfold vecConv
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [liftQ, translateFun, MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]
  intro g f₀ l hl
  induction l with
  | zero => rfl
  | succ l ih =>
    funext x
    simp only [FeedForwardNet.act]
    rw [ih (by omega), hconv l (by omega)]
    rfl

