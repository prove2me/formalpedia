-- Prove2me | solution 1 for Finset.popular_pairs_card_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:44.302573+00:00
-- url     : https://prove2.me/submissions/89c363fa-f1da-4828-a22d-403fa8552365

import Mathlib
import Theorems.Thm_Finset_sum_addConvolution_eq_card_product

open scoped Pointwise
namespace Finset

/--
Additive energy as a sum of squared fiber counts. Restatement of
Mathlib `Finset.addEnergy_eq_sum_sq` in terms of the convolution
`X.addConvolution Y`; the energy equals `Σ_{s ∈ X+Y} r(s)²` where
`r(s)` is the number of pairs `(x,y)` summing to `s`.
-/
lemma addEnergy_eq_sum_addConvolution_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    Finset.addEnergy X Y = ∑ s ∈ X + Y, (X.addConvolution Y s) ^ 2 := by
  simp_rw [Finset.addConvolution]
  exact Finset.addEnergy_eq_sum_sq' X Y

/--
Split the energy sum into rare-fiber and popular-fiber parts at
threshold `θ`. The two filters partition `X + Y` (over `<` vs `≥`),
so combining them recovers the full `Σ r(s)²` form of
`Finset.addEnergy`.
-/
lemma addEnergy_split_by_threshold {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) =
      (∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
        (X.addConvolution Y s) ^ 2) +
      (∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2) := by
  rw [addEnergy_eq_sum_addConvolution_sq,
    ← Finset.sum_filter_add_sum_filter_not (X + Y) (fun s ↦ X.addConvolution Y s < θ)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  apply Finset.filter_congr
  intros
  omega

/--
Popular-difference lemma (sum form). The rare part of `Σ r(s)²`
(over fibers with `r(s) < θ`) is bounded by `θ · |X| · |Y|`, because
`r(s)² ≤ θ · r(s)` on the rare set and `Σ r(s) = |X|·|Y|`
(`sum_addConvolution_eq_card_product`). Therefore
`E[X,Y] ≤ θ·|X|·|Y| + (popular part)`, giving the popular-sum set
its energy bound for the random-restriction step.
-/
lemma addEnergy_le_popular_part {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) ≤ θ * (X.card * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2 := by
  rw [addEnergy_split_by_threshold X Y θ]
  refine Nat.add_le_add_right ?_ _
  calc ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          (X.addConvolution Y s) ^ 2
      ≤ ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          θ * X.addConvolution Y s := by
        refine Finset.sum_le_sum fun s hs ↦ ?_
        rw [Finset.mem_filter] at hs
        have hle : X.addConvolution Y s ≤ θ := Nat.le_of_lt hs.2
        rw [pow_two]
        exact Nat.mul_le_mul_right _ hle
    _ = θ * ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          X.addConvolution Y s := by rw [Finset.mul_sum]
    _ ≤ θ * ∑ s ∈ X + Y, X.addConvolution Y s :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ = θ * (X.card * Y.card) := by rw [sum_addConvolution_eq_card_product]

end Finset

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (_hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η / 2 * (X.card : ℝ) * Y.card ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYcard : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
  have hsplit_nat := addEnergy_le_popular_part X Y θ
  have hsplit : (Finset.addEnergy X Y : ℝ) ≤
      θ * ((X.card : ℝ) * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hsplit_nat
    push_cast at h
    exact h
  have hθBd : (θ : ℝ) * ((X.card : ℝ) * Y.card) ≤ η / 2 * (X.card : ℝ) ^ 3 := by
    rw [hYcard]
    have hθ' : (θ : ℝ) ≤ η / 2 * X.card := by linarith
    have hsq_nn : (0 : ℝ) ≤ (X.card : ℝ) ^ 2 := sq_nonneg _
    have hmul : (θ : ℝ) * (X.card : ℝ) ^ 2 ≤ (η / 2 * X.card) * (X.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hθ' hsq_nn
    nlinarith [hmul]
  have hpopSqLB : η / 2 * (X.card : ℝ) ^ 3 ≤
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by linarith
  have hsqLE : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 ≤
      (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s _ ↦ ?_)
    have hrLE : X.addConvolution Y s ≤ X.card :=
      Finset.addConvolution_le_card_left
    have hrLE' : ((X.addConvolution Y s : ℝ)) ≤ (X.card : ℝ) := by exact_mod_cast hrLE
    have hr_nn : (0 : ℝ) ≤ ((X.addConvolution Y s : ℝ)) := by positivity
    nlinarith
  have hfiber_nat : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        X.addConvolution Y s =
      ((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card := by
    simp only [Finset.addConvolution]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_congr
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    constructor
    · intro h
      have h' : a + b ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) := h
      exact (Finset.mem_filter.mp h').2
    · intro h
      have h' : a + b ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) :=
        Finset.mem_filter.mpr ⟨Finset.add_mem_add hp.1 hp.2, h⟩
      exact h'
  have hcombined : η / 2 * (X.card : ℝ) ^ 3 ≤
      (X.card : ℝ) *
      (((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    calc η / 2 * (X.card : ℝ) ^ 3
        ≤ ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) ^ 2 := hpopSqLB
      _ ≤ (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) := hsqLE
      _ = (X.card : ℝ) *
            (((X ×ˢ Y).filter
              (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
          congr 1
          exact_mod_cast hfiber_nat
  have hdiv : η / 2 * (X.card : ℝ) ^ 2 ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    have heq : η / 2 * (X.card : ℝ) ^ 3 =
        (X.card : ℝ) * (η / 2 * (X.card : ℝ) ^ 2) := by ring
    rw [heq] at hcombined
    exact le_of_mul_le_mul_left hcombined hXpos
  have hgoal : η / 2 * (X.card : ℝ) * Y.card = η / 2 * (X.card : ℝ) ^ 2 := by
    rw [hYcard]; ring
  linarith
