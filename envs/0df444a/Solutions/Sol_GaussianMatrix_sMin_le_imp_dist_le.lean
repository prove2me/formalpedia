-- Prove2me | solution 1 for GaussianMatrix.sMin_le_imp_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T04:05:22.712407+00:00
-- url     : https://prove2.me/submissions/c28ac183-70d6-4f46-9820-6a3e2fbc7340

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- `‖A (c • x)‖ = |c| ‖A x‖` in the `sqrt (v ⬝ᵥ v)` form. -/
theorem sqrt_dot_mulVec_smul {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    Real.sqrt ((A *ᵥ (c • x)) ⬝ᵥ (A *ᵥ (c • x))) = |c| * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]

/-- For a unit vector `x`, some column distance is at most `√n ‖A x‖`. -/
theorem exists_dist_le_of_unit {N n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin N) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ x = 1) :
    ∃ j : Fin n, (⨅ y : {y : Fin n → ℝ // y j = 1}, Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1)))
      ≤ Real.sqrt n * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|) hne
  refine ⟨j, ?_⟩
  -- `1 ≤ n * x_j²`
  have hsum : (1 : ℝ) ≤ n * x j ^ 2 := by
    have h1 : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
    have h2 : ∑ i, x i ^ 2 ≤ ∑ _i : Fin n, x j ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hj i (Finset.mem_univ _)
      rw [← sq_abs (x i), ← sq_abs (x j)]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    linarith
  have hxj : x j ≠ 0 := by
    intro h; rw [h] at hsum; norm_num at hsum
  have hxa : 0 < |x j| := abs_pos.2 hxj
  -- `1 ≤ √n |x_j|`
  have hsq : 1 ≤ Real.sqrt n * |x j| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (Nat.cast_nonneg n)]
    exact Real.one_le_sqrt.2 hsum
  set y : Fin n → ℝ := (x j)⁻¹ • x with hy
  have hyj : y j = 1 := by simp [hy, hxj]
  have hbdd : BddBelow (Set.range fun y : {y : Fin n → ℝ // y j = 1} =>
      Real.sqrt ((A *ᵥ y.1) ⬝ᵥ (A *ᵥ y.1))) :=
    ⟨0, by rintro _ ⟨y, rfl⟩; exact Real.sqrt_nonneg _⟩
  refine (ciInf_le hbdd ⟨y, hyj⟩).trans ?_
  show Real.sqrt ((A *ᵥ y) ⬝ᵥ (A *ᵥ y)) ≤ _
  rw [hy, sqrt_dot_mulVec_smul, abs_inv]
  set F := Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  rw [inv_mul_le_iff₀ hxa]
  nlinarith

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin N) (Fin n) ℝ) (s : ℝ)
    (hs : sMin A ≤ s) :
    ∃ j : Fin n, (⨅ x : {x : Fin n → ℝ // x j = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)))
      ≤ Real.sqrt n * s := by
  set D : Fin n → ℝ := fun j =>
    ⨅ x : {x : Fin n → ℝ // x j = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) with hD
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_min_image Finset.univ D hne
  refine ⟨j₀, ?_⟩
  have hn0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  -- `D j₀ / √n ≤ sMin A`
  have : Nonempty {x : Fin n → ℝ // x ⬝ᵥ x = 1} :=
    ⟨⟨Pi.single ⟨0, hn⟩ 1, by simp [dotProduct, Pi.single_apply]⟩⟩
  have hlow : D j₀ / Real.sqrt n ≤ sMin A := by
    unfold sMin
    refine le_ciInf fun x => ?_
    obtain ⟨j, hj⟩ := exists_dist_le_of_unit hn A x.1 x.2
    rw [div_le_iff₀ hn0]
    calc D j₀ ≤ D j := hj₀ j (Finset.mem_univ _)
      _ ≤ _ := by rw [mul_comm]; exact hj
  have := (div_le_iff₀ hn0).1 (hlow.trans hs)
  linarith
