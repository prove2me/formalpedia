-- Prove2me | solution 1 for BidPriceControl.Asymptotic.relaxed_value_scaling
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:55:28.678824+00:00
-- url     : https://prove2.me/submissions/a79134ae-6d1d-47aa-85ab-b8b955a9690e

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model

open MeasureTheory ProbabilityTheory

namespace Aux_BPC_scaling

lemma sum_Icc_one (N : ℕ) (f : ℕ → ℝ) :
    ∑ t ∈ Finset.Icc 1 N, f t = ∑ u ∈ Finset.range N, f (u + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma block (θ : ℕ) (hθ : 1 ≤ θ) (G : ℕ → ℝ) (k : ℕ) :
    ∑ u ∈ Finset.range (θ * k), G ((u + θ) / θ) = (θ : ℝ) * ∑ u ∈ Finset.range k, G (u + 1) := by
  have hθ0 : 0 < θ := hθ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have : ∀ i ∈ Finset.range θ, G ((θ * k + i + θ) / θ) = G (k + 1) := by
      intro i hi
      have hi' : i < θ := Finset.mem_range.mp hi
      have e : θ * k + i + θ = i + θ * (k + 1) := by ring
      rw [e, Nat.add_mul_div_left _ _ hθ0, Nat.div_eq_of_lt hi', zero_add]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma block_Icc (θ : ℕ) (hθ : 1 ≤ θ) (G : ℕ → ℝ) (k : ℕ) :
    ∑ t ∈ Finset.Icc 1 (θ * k), G ((t + θ - 1) / θ) = (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, G t := by
  rw [sum_Icc_one, sum_Icc_one, ← block θ hθ G k]
  apply Finset.sum_congr rfl
  intro u _
  congr 2
  omega

end Aux_BPC_scaling

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ) (F : ℕ → Measure (Fin n → ℝ))
    (k : ℕ) (x : Fin m → ℕ) (θ : ℕ) (hθ : 1 ≤ θ) :
    (∀ μ : Fin m → ℝ,
      relaxedValue A (scaledLaw F θ) (θ * k) (θ • x) μ = (θ : ℝ) * relaxedValue A F k x μ) ∧
    ∀ μstar : Fin m → ℝ, IsRelaxedMinimizer A F k x μstar →
      IsRelaxedMinimizer A (scaledLaw F θ) (θ * k) (θ • x) μstar := by
  have hscale : ∀ μ : Fin m → ℝ,
      relaxedValue A (scaledLaw F θ) (θ * k) (θ • x) μ = (θ : ℝ) * relaxedValue A F k x μ := by
    intro μ
    unfold relaxedValue scaledLaw
    rw [mul_add]
    congr 1
    · exact Aux_BPC_scaling.block_Icc θ hθ
        (fun s => ∑ j, ∫ r, max (r j - bidSum A μ j) 0 ∂(F s)) k
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
      ring
  refine ⟨hscale, ?_⟩
  intro μstar ⟨h0, hmin⟩
  refine ⟨h0, fun μ hμ => ?_⟩
  rw [hscale, hscale]
  exact mul_le_mul_of_nonneg_left (hmin μ hμ) (Nat.cast_nonneg θ)
