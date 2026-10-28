-- Prove2me | solution 1 for FunctionalInequalities.Analysis.CoordinateTensor.drift_expression_ge_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:28:39.22308+00:00
-- url     : https://prove2.me/submissions/30fa13a4-0bd5-4812-b323-2f3cfe475a01

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_SlotAction
import Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_bound_readable

noncomputable section
open Matrix
variable {n r : ℕ}
private lemma FunctionalInequalities.Analysis.CoordinateTensor.cross_bound (x y : (Fin r → Fin n) → ℝ) :
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y ≤ -2 * inner x y := by
  calc
    -(1 / 2 : ℝ) * inner x x - 2 * inner y y =
        ∑ J, (-(1 / 2 : ℝ) * (x J * x J) - 2 * (y J * y J)) := by
          unfold inner
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ∑ J, (-2 * (x J * y J)) := by
      apply Finset.sum_le_sum
      intro J hJ
      nlinarith [sq_nonneg (x J - 2 * y J)]
    _ = -2 * inner x y := by
      unfold inner
      rw [Finset.mul_sum]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.actSum_bound (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (T : (Fin r → Fin n) → ℝ) :
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
      (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
  classical
  have hi (i : Fin n) :
      inner (actSum (H i) T) (actSum (H i) T) ≤
        (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
    unfold inner actSum
    calc
      ∑ J, (∑ s, actOn (H i) s T J) * (∑ s, actOn (H i) s T J) ≤
          ∑ J, (r : ℝ) * ∑ s, (actOn (H i) s T J) * (actOn (H i) s T J) := by
            apply Finset.sum_le_sum
            intro J hJ
            simpa only [pow_two, Finset.card_univ, Fintype.card_fin] using
              (sq_sum_le_card_mul_sum_sq
                (s := (Finset.univ : Finset (Fin r)))
                (f := fun s : Fin r => actOn (H i) s T J))
      _ = (r : ℝ) * ∑ s, ∑ J,
            (actOn (H i) s T J) * (actOn (H i) s T J) := by
            rw [← Finset.mul_sum, Finset.sum_comm]
  calc
    ∑ i, inner (actSum (H i) T) (actSum (H i) T) ≤
        ∑ i, (r : ℝ) * ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          apply Finset.sum_le_sum
          intro i hi'
          exact hi i
    _ = (r : ℝ) * ∑ i, ∑ s, inner (actOn (H i) s T) (actOn (H i) s T) := by
          rw [Finset.mul_sum]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.fin_sum_const_mul (q : ℕ) (x : ℝ) :
    (∑ _ : Fin q, x) = (q : ℝ) * x := by
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
private lemma FunctionalInequalities.Analysis.CoordinateTensor.sum_sq_nonneg {α : Type*} [Fintype α] (f : α → ℝ) :
    0 ≤ ∑ x, f x ^ 2 := by
  exact Finset.sum_nonneg (fun x hx => sq_nonneg (f x))
/-- **The algebra of BKL Lemma 5.1, (89)–(91)** at `A = Id`: for symmetric `H_i` with `Σ_i H_i² ≤ 8 Id` and any
tensors `T, W_i, L` of order `r = m − 1 ≥ 1`, the drift expression of (89),
`−(m+1)|T|² − 2⟨T, L⟩ + Σ|W_i|² − 2Σ⟨W_i, Σ_{H_i}T⟩ + ½Σ|Σ_{H_i}T|² + ½ΣΣ_s|H_i^{(s)}T|²`, is at least
`½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩`. -/
theorem solution {m : ℕ} (hm : r + 1 = m) (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i, (H i).IsHermitian)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T L : (Fin r → Fin n) → ℝ) (W : Fin n → (Fin r → Fin n) → ℝ) :
    (1 / 2 : ℝ) * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i) - 17 * (m : ℝ) ^ 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T T - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T L ≤
      -((m : ℝ) + 1) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T - 2 * FunctionalInequalities.Analysis.CoordinateTensor.inner T L + ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i)
        - 2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
        + (1 / 2 : ℝ) * ∑ i, ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) := by
  classical
  have hH_used : (0 : ℝ) ≤ 0 := by
    exact (fun _ : ∀ i, (H i).IsHermitian => le_rfl) hH
  have hcross :
      -(1 / 2 : ℝ) * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i) -
          2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) ≤
        -2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) := by
    have hi (i : Fin n) := FunctionalInequalities.Analysis.CoordinateTensor.cross_bound (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)
    calc
      -(1 / 2 : ℝ) * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i) -
            2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) =
          ∑ i, (-(1 / 2 : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (W i) -
            2 * FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T)) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ ∑ i, -2 * FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) := by
            apply Finset.sum_le_sum
            intro i hi'
            exact hi i
      _ = -2 * ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (W i) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) := by
            rw [Finset.mul_sum]
  have hslot :
      ∑ i, ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) ≤
        8 * (r : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T := by
    calc
      ∑ i, ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) =
          ∑ s, ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) := by
            rw [Finset.sum_comm]
      _ ≤ ∑ s, 8 * ∑ J, T J ^ 2 := by
            apply Finset.sum_le_sum
            intro s hs
            simpa only [FunctionalInequalities.Analysis.CoordinateTensor.inner, FunctionalInequalities.Analysis.CoordinateTensor.actOn, pow_two] using FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_readable H h8 T s
      _ = 8 * (r : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T := by
            rw [FunctionalInequalities.Analysis.CoordinateTensor.fin_sum_const_mul]
            unfold FunctionalInequalities.Analysis.CoordinateTensor.inner
            simp only [pow_two]
            ring
  have hact := FunctionalInequalities.Analysis.CoordinateTensor.actSum_bound H T
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hC :
      ∑ i, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) (FunctionalInequalities.Analysis.CoordinateTensor.actSum (H i) T) ≤
        (r : ℝ) * (8 * (r : ℝ) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T) :=
    le_trans hact (mul_le_mul_of_nonneg_left hslot hr)
  have hA : 0 ≤ FunctionalInequalities.Analysis.CoordinateTensor.inner T T := by
    unfold FunctionalInequalities.Analysis.CoordinateTensor.inner
    simpa only [pow_two] using FunctionalInequalities.Analysis.CoordinateTensor.sum_sq_nonneg T
  have hDnonneg :
      0 ≤ ∑ i, ∑ s, FunctionalInequalities.Analysis.CoordinateTensor.inner (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T) := by
    simp only [FunctionalInequalities.Analysis.CoordinateTensor.inner]
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro s hs
    simpa only [pow_two] using FunctionalInequalities.Analysis.CoordinateTensor.sum_sq_nonneg (FunctionalInequalities.Analysis.CoordinateTensor.actOn (H i) s T)
  have hmcast : (m : ℝ) = (r : ℝ) + 1 := by
    exact_mod_cast hm.symm
  have hcoef :
      0 ≤ 17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2 := by
    rw [hmcast]
    nlinarith [sq_nonneg (r : ℝ)]
  have hprod :
      0 ≤ (17 * (m : ℝ) ^ 2 - (m : ℝ) - 1 - 16 * (r : ℝ) ^ 2) * FunctionalInequalities.Analysis.CoordinateTensor.inner T T :=
    mul_nonneg hcoef hA
  nlinarith [hcross, hC, hA, hDnonneg, hprod, hH_used]
