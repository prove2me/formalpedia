-- Prove2me | solution 1 for DetANN.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T03:05:08.154583+00:00
-- url     : https://prove2.me/submissions/c83672a6-6674-4907-9986-70d0f3a4e657

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice
import Theorems.Thm_DetANN_rademacher_moments

open DetANN

namespace DetANNL62Aux

/-! ### Averages -/

lemma avgOver_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    avgOver f = avgOver (f ∘ e) := by
  unfold avgOver
  rw [Fintype.card_congr e, Function.comp_def, e.sum_comp f]

lemma avgOver_prod_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    avgOver (fun p : α × β => f p.1 * g p.2) = avgOver f * avgOver g := by
  unfold avgOver
  rw [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma avgOver_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    avgOver (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avgOver (f i) := by
  unfold avgOver
  rw [Finset.sum_comm, Finset.mul_sum]

lemma avgOver_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avgOver (fun a => c * f a) = c * avgOver f := by
  unfold avgOver
  rw [← Finset.mul_sum]; ring

lemma avgOver_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avgOver (fun _ : α => c) = c := by
  unfold avgOver
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ### Item 3: Lemma 6.2 -/

lemma blocks_normSq {d L : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin L → Fin d → Bool)
    (j : Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    ‖signedBlocks h L ξ j z‖ ^ 2 =
      ∑ ℓ : Fin L, ((Real.sqrt ((L : ℝ) * d))⁻¹ * ∑ r : Fin d, h j r * signOf (ξ ℓ r) * z r) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [signedBlocks, Real.norm_eq_abs, sq_abs]
  congr 1
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- `d‖A_j v‖² − ‖v‖² = (1/L) ∑_ℓ (Y_ℓ² − ‖v‖²)` with `Y_ℓ = ∑_r h_{jr} v_r ξ^(ℓ)_r`. -/
lemma identity_23' {d L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) (h : Matrix (Fin d) (Fin d) ℝ)
    (ξ : Fin L → Fin d → Bool) (j : Fin d) (v : EuclideanSpace ℝ (Fin d)) :
    (d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2 =
      (1 / (L : ℝ)) * ∑ ℓ : Fin L, ((∑ r, h j r * v r * signOf (ξ ℓ r)) ^ 2 - ‖v‖ ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [blocks_normSq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hc : ((Real.sqrt ((L : ℝ) * d))⁻¹) ^ 2 = 1 / ((L : ℝ) * d) := by
    rw [inv_pow, Real.sq_sqrt (by positivity), one_div]
  have hterm : ∀ ℓ : Fin L, ((Real.sqrt ((L : ℝ) * d))⁻¹ *
      ∑ r : Fin d, h j r * signOf (ξ ℓ r) * v r) ^ 2 =
      1 / ((L : ℝ) * d) * (∑ r, h j r * v r * signOf (ξ ℓ r)) ^ 2 := by
    intro ℓ
    rw [mul_pow, hc]
    congr 2
    exact Finset.sum_congr rfl fun r _ => by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp

/-- The sign sum of a completed row splits into the fixed part and the free part. -/
lemma Y_complete {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u ξ : Fin L → Fin d → Bool)
    (j : Fin d) (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) :
    ∑ r, h j r * v r * signOf (completeSigns μ u ξ ℓ r) =
      fixedPart h μ u j v ℓ + ∑ r, freeCoeff h μ j v ℓ r * signOf (ξ ℓ r) := by
  rw [fixedPart, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [completeSigns, freeCoeff]
  split_ifs <;> ring

end DetANNL62Aux

open DetANNL62Aux in
theorem solution {d : ℕ} (hd : 1 ≤ d) (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (hL : 1 ≤ L)
    (τ : ℝ) (p₀ : ℕ) (D : Finset (EuclideanSpace ℝ (Fin d))) (μ u : Fin L → Fin d → Bool) :
    condPotential h L τ p₀ D μ u = lemma62Expr h L τ p₀ D μ u := by
  have hLR : (L : ℝ) ≠ 0 := by have : (0 : ℝ) < L := by exact_mod_cast hL
                               exact this.ne'
  unfold condPotential lemma62Expr potential
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [avgOver_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  -- rewrite each term as a constant times the `2p₀`-th power of a sum of independent rows
  set X' : Fin L → (Fin d → Bool) → ℝ := fun ℓ s =>
    (fixedPart h μ u j v ℓ + ∑ r, freeCoeff h μ j v ℓ r * signOf (s r)) ^ 2 - ‖v‖ ^ 2 with hX'
  have hpt : (fun ξ : Fin L → Fin d → Bool =>
      (((d : ℝ) * ‖signedBlocks h L (completeSigns μ u ξ) j v‖ ^ 2 - ‖v‖ ^ 2) /
        (τ * ‖v‖ ^ 2)) ^ (2 * p₀)) =
      fun ξ => (((L : ℝ) * τ * ‖v‖ ^ 2) ^ (2 * p₀))⁻¹ * (∑ ℓ : Fin L, X' ℓ (ξ ℓ)) ^ (2 * p₀) := by
    funext ξ
    rw [identity_23' hd hL]
    simp_rw [Y_complete, hX']
    rw [one_div_mul_eq_div, div_div, ← mul_assoc, div_pow, div_eq_inv_mul]
  rw [hpt, avgOver_const_mul, rademacher_moments.2 (Fin d → Bool) L X' (2 * p₀)]
  have hprod : (∏ ℓ : Fin L, egf fun k => avgOver fun s => X' ℓ s ^ k) =
      ∏ ℓ : Fin L, egf fun k =>
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (-‖v‖ ^ 2) ^ (k - i) *
          ((2 * i).factorial : ℝ) * PowerSeries.coeff (2 * i)
            (expSeries (fixedPart h μ u j v ℓ) * ∏ r, coshSeries (freeCoeff h μ j v ℓ r)) := by
    refine Finset.prod_congr rfl fun ℓ _ => congrArg egf (funext fun k => ?_)
    -- moments of `X = Y² − ‖v‖²` from those of `Y`
    have hX : (fun s : Fin d → Bool => X' ℓ s ^ k) =
        fun s => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (-‖v‖ ^ 2) ^ (k - i) *
          (fixedPart h μ u j v ℓ + ∑ r, freeCoeff h μ j v ℓ r * signOf (s r)) ^ (2 * i) := by
      funext s
      rw [hX']; dsimp only; rw [sub_eq_add_neg, add_pow]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← pow_mul, mul_comm 2 i]; ring
    rw [hX, avgOver_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [avgOver_const_mul, rademacher_moments.1]
    ring
  rw [hprod]
  ring
