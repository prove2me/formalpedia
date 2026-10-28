-- Prove2me | solution 1 for AvramDividend.Classical.levy_equal_mesh_increment_reversal_rectangles_ws01e_b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:17:24.742882+00:00
-- url     : https://prove2.me/submissions/ca8ea0e0-b66a-4dab-98cd-5f9adf85e0fd

import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Fin2
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finitePrefix_increment_rectangle_product
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
/-- Equal-mesh finite-dimensional Lévy increment reversal, on every Borel rectangle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (δ : ℝ≥0) (n : ℕ) (B : Fin n → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i)) :
    P {ω | (fun i : Fin n => X.X (((i.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.val : ℝ≥0) * δ) ω) ∈ Set.pi Set.univ B} =
    P {ω | (fun i : Fin n => X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * δ) ω -
      X.X ((i.rev.val : ℝ≥0) * δ) ω) ∈ Set.pi Set.univ B} := by
  let t : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
  have ht : Monotone t := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) bot_le
  have hstep (k : ℕ) : t (k + 1) - t k = δ := by
    simp [t, Nat.cast_add, add_mul]
  have hIncr (k : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
      P {ω | X.X (t (k + 1)) ω - X.X (t k) ω ∈ A} =
      P {ω | X.X δ ω ∈ A} := by
    have hd := X.stationaryIncrements (t k) (t (k + 1)) (ht (Nat.le_succ k))
    rw [hstep k] at hd
    exact hd.measure_mem_eq hA
  have hrect (C : Fin n → Set ℝ) (hC : ∀ i, MeasurableSet (C i)) :
      P {ω | (fun i : Fin n => X.X (t (i.val + 1)) ω -
        X.X (t i.val) ω) ∈ Set.pi Set.univ C} =
      ∏ i : Fin n, P {ω | X.X δ ω ∈ C i} := by
    calc
      _ = ∏ k ∈ Finset.range n, P {ω | X.X (t (k + 1)) ω -
          X.X (t k) ω ∈ (if hk : k < n then C ⟨k, hk⟩ else Set.univ)} :=
        levy_finitePrefix_increment_rectangle_product X 0 t ht bot_le n C hC
      _ = ∏ i : Fin n, P {ω | X.X δ ω ∈ C i} := by
        have hfin : (∏ i : Fin n, P {ω | X.X δ ω ∈ C i}) =
            ∏ k ∈ Finset.range n, P {ω | X.X δ ω ∈
              (if hk : k < n then C ⟨k, hk⟩ else Set.univ)} := by
          simpa using (Fin.prod_univ_eq_prod_range
            (fun k : ℕ => P {ω | X.X δ ω ∈
              (if hk : k < n then C ⟨k, hk⟩ else Set.univ)}) n)
        rw [hfin]
        apply Finset.prod_congr rfl
        intro k hk
        have hkn : k < n := Finset.mem_range.mp hk
        simpa only [dif_pos hkn] using hIncr k (C ⟨k, hkn⟩) (hC _)
  have hswap : (∏ i : Fin n, P {ω | X.X δ ω ∈ B i}) =
      ∏ i : Fin n, P {ω | X.X δ ω ∈ B i.rev} := by
    let e : Fin n ≃ Fin n :=
      { toFun := Fin.rev, invFun := Fin.rev,
        left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
    exact (Fintype.prod_equiv e
      (fun i : Fin n => P {ω | X.X δ ω ∈ B i.rev})
      (fun i : Fin n => P {ω | X.X δ ω ∈ B i})
      (by intro i; rfl)).symm
  change P {ω | (fun i : Fin n => X.X (t (i.val + 1)) ω -
    X.X (t i.val) ω) ∈ Set.pi Set.univ B} =
    P {ω | (fun i : Fin n => X.X (t (i.rev.val + 1)) ω -
      X.X (t i.rev.val) ω) ∈ Set.pi Set.univ B}
  have hrev : {ω | (fun i : Fin n => X.X (t (i.rev.val + 1)) ω -
        X.X (t i.rev.val) ω) ∈ Set.pi Set.univ B} =
      {ω | (fun i : Fin n => X.X (t (i.val + 1)) ω -
        X.X (t i.val) ω) ∈ Set.pi Set.univ (fun i => B i.rev)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor <;> intro h i <;>
      simpa only [Fin.rev_rev] using h i.rev
  calc
    _ = ∏ i : Fin n, P {ω | X.X δ ω ∈ B i} := hrect B hB
    _ = ∏ i : Fin n, P {ω | X.X δ ω ∈ B i.rev} := hswap
    _ = _ := by
      rw [hrev]
      exact (hrect (fun i => B i.rev) (fun i => hB _)).symm
