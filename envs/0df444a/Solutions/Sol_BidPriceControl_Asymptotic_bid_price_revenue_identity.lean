-- Prove2me | solution 1 for BidPriceControl.Asymptotic.bid_price_revenue_identity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T10:02:46.940254+00:00
-- url     : https://prove2.me/submissions/ca1c58a8-7d5f-421f-aecb-5dbd63898529

import Mathlib
import Definitions.Def_BidPriceControl_Asymptotic_Model
import Theorems.Thm_BidPriceControl_Asymptotic_kuhn_tucker_conditions

open MeasureTheory ProbabilityTheory

namespace Aux_BPC_bpr

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

end Aux_BPC_bpr

open BidPriceControl.Asymptotic in
theorem solution {m n : ℕ} (A : Fin m → Fin n → ℕ)
    (F : ℕ → Measure (Fin n → ℝ)) (k : ℕ) (x : Fin m → ℕ)
    (hF : ∀ t ∈ Finset.Icc 1 k, IsRequestLaw (F t))
    (μstar : Fin m → ℝ) (hmin : IsRelaxedMinimizer A F k x μstar) (θ : ℕ) (hθ : 1 ≤ θ) :
    ∑ t ∈ Finset.Icc 1 (θ * k), ∑ j, exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j
      = (θ : ℝ) * ∑ i, μstar i * (x i : ℝ) := by
  have h1 : ∑ t ∈ Finset.Icc 1 (θ * k), ∑ j,
      exceedProb A (scaledLaw F θ) μstar t j * bidSum A μstar j
      = (θ : ℝ) * ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * bidSum A μstar j :=
    Aux_BPC_bpr.block_Icc θ hθ (fun s => ∑ j, exceedProb A F μstar s j * bidSum A μstar j) k
  rw [h1]
  congr 1
  have hKT : ∀ i, μstar i * (∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))
      = μstar i * (x i : ℝ) := by
    intro i
    have := (kuhn_tucker_conditions A F k x hF μstar hmin i).2
    linarith [this, mul_sub (μstar i) (x i : ℝ)
      (∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (A i j : ℝ))]
  rw [← Finset.sum_congr rfl (fun i _ => hKT i)]
  unfold bidSum
  simp only [Finset.mul_sum]
  calc ∑ t ∈ Finset.Icc 1 k, ∑ j, ∑ i, exceedProb A F μstar t j * (μstar i * (A i j : ℝ))
      = ∑ t ∈ Finset.Icc 1 k, ∑ i, ∑ j, exceedProb A F μstar t j * (μstar i * (A i j : ℝ)) :=
        Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ i, ∑ t ∈ Finset.Icc 1 k, ∑ j, exceedProb A F μstar t j * (μstar i * (A i j : ℝ)) :=
        Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro t _
        apply Finset.sum_congr rfl; intro j _
        ring
