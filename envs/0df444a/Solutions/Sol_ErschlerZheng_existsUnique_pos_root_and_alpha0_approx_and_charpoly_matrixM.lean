-- Prove2me | solution 1 for ErschlerZheng.existsUnique_pos_root_and_alpha0_approx_and_charpoly_matrixM
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-06T02:56:19.27564+00:00
-- url     : https://prove2.me/submissions/49e46390-2785-4db0-97c0-4369b0f44281

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

section
/-!
# The cubic `x³ - x² - 2x - 4`: positive roots exceed 2 and lie in `(2.4675, 2.4676)`
-/

namespace ErschlerZheng

namespace CubicBase

theorem pos_root_gt_two {x : ℝ} (hx : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) : 2 < x := by
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hc), mul_nonneg (mul_nonneg hx.le hx.le)
    (sub_nonneg.mpr hc)]

theorem pos_root_gt {x : ℝ} (h0 : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) :
    (24675 : ℝ) / 10000 < x := by
  have h2 := pos_root_gt_two h0 h
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le)) h0.le]

theorem pos_root_lt {x : ℝ} (h0 : 0 < x) (h : x ^ 3 - x ^ 2 - 2 * x - 4 = 0) :
    x < (24676 : ℝ) / 10000 := by
  have h2 := pos_root_gt_two h0 h
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr h2.le)) h0.le]

end CubicBase

end ErschlerZheng
end

section
/-!
# A19: the constants `λ_0`, `α_0`, `η_0` and the characteristic polynomial of `M`

`f(x) = x³ - x² - 2x - 4` has `f ⩽ -4` on `(0, 2]` and is increasing on `[2, ∞)`, so it has one
positive root, `λ_0 ∈ (2.4675, 2.4676)`. A complex root `z` has `|z|³ ⩽ |z|² + 2|z| + 4`, so
`|z| ⩽ λ_0`. `α_0` is bounded through `exp` (Taylor bound) and the bounds on `log 2`.
-/

namespace ErschlerZheng

namespace ConstantsDev

open CubicBase

theorem root_unique {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h1 : x ^ 3 - x ^ 2 - 2 * x - 4 = 0)
    (h2 : y ^ 3 - y ^ 2 - 2 * y - 4 = 0) : x = y := by
  have hx2 := pos_root_gt_two hx h1
  have hy2 := pos_root_gt_two hy h2
  have hfac : (x - y) * (x ^ 2 + x * y + y ^ 2 - x - y - 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · nlinarith

theorem exists_root : ∃ x : ℝ, 0 < x ∧ x ^ 3 - x ^ 2 - 2 * x - 4 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x - 4) (Set.Icc 2 3) := by fun_prop
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by norm_num : (2 : ℝ) ≤ 3) hc
    (show (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x - 4) 2)
      ((fun x : ℝ => x ^ 3 - x ^ 2 - 2 * x - 4) 3) by norm_num)
  exact ⟨x, by linarith [hx.1], hfx⟩

theorem lambda0_spec : 0 < lambda0 ∧ lambda0 ^ 3 - lambda0 ^ 2 - 2 * lambda0 - 4 = 0 := by
  obtain ⟨x, hx, hfx⟩ := exists_root
  have hset : {x : ℝ | 0 < x ∧ x ^ 3 - x ^ 2 - 2 * x - 4 = 0} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨hy, hfy⟩ => root_unique hy hx hfy hfx, fun h => h ▸ ⟨hx, hfx⟩⟩
  unfold lambda0
  rw [hset, csSup_singleton]
  exact ⟨hx, hfx⟩

theorem lambda0_gt : (24675 : ℝ) / 10000 < lambda0 :=
  pos_root_gt lambda0_spec.1 lambda0_spec.2

theorem lambda0_lt : lambda0 < (24676 : ℝ) / 10000 :=
  pos_root_lt lambda0_spec.1 lambda0_spec.2

theorem exp_lower_aux : Real.exp (90319 / 100000) < 24675 / 10000 := by
  have h := Real.exp_bound (x := 90319 / 100000) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 14) (by norm_num)
  have h' := (abs_le.mp h).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_pos] at h'
  linarith

theorem exp_upper_aux : 24676 / 10000 < Real.exp (90329 / 100000) := by
  have h := Real.exp_bound (x := 90329 / 100000) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (n := 14) (by norm_num)
  have h' := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_pos] at h'
  linarith

theorem log_lambda0_bounds :
    (90319 : ℝ) / 100000 < Real.log lambda0 ∧ Real.log lambda0 < 90329 / 100000 := by
  have h0 := lambda0_spec.1
  constructor
  · rw [Real.lt_log_iff_exp_lt h0]
    linarith [exp_lower_aux, lambda0_gt]
  · rw [Real.log_lt_iff_lt_exp h0]
    linarith [exp_upper_aux, lambda0_lt]

theorem alpha0_approx : |alpha0 - 7674 / 10000| < 5 / 100000 := by
  obtain ⟨hl, hu⟩ := log_lambda0_bounds
  have l2l := Real.log_two_gt_d9
  have l2u := Real.log_two_lt_d9
  have hpos : 0 < Real.log lambda0 := by linarith
  unfold alpha0
  rw [abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hpos]
    nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hpos]
    nlinarith

theorem charpoly_matrixM : (matrixM.map (Nat.cast : ℕ → ℤ)).charpoly =
    Polynomial.X ^ 3 - Polynomial.X ^ 2 - 2 * Polynomial.X - 4 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [matrixM]
  ring

theorem norm_root_le (z : ℂ) (hz : z ^ 3 - z ^ 2 - 2 * z - 4 = 0) : ‖z‖ ≤ lambda0 := by
  obtain ⟨h0, h⟩ := lambda0_spec
  have h2 := pos_root_gt_two h0 h
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  have hz3 : z ^ 3 = z ^ 2 + 2 * z + 4 := by linear_combination hz
  have hle : r ^ 3 ≤ r ^ 2 + 2 * r + 4 := by
    have := congrArg norm hz3
    rw [norm_pow] at this
    rw [hr, this]
    calc ‖z ^ 2 + 2 * z + 4‖ ≤ ‖z ^ 2 + 2 * z‖ + ‖(4 : ℂ)‖ := norm_add_le _ _
      _ ≤ ‖z ^ 2‖ + ‖2 * z‖ + ‖(4 : ℂ)‖ := by gcongr; exact norm_add_le _ _
      _ = ‖z‖ ^ 2 + 2 * ‖z‖ + 4 := by simp [norm_pow]
  by_contra hc
  push Not at hc
  nlinarith [mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr h2.le),
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr h2.le)) h0.le,
    mul_pos (sub_pos.mpr hc) (sub_pos.mpr hc)]

theorem eta_spec : ∃ η : ℝ, η ^ 3 + η ^ 2 + η - 2 = 0 ∧
    (∀ y : ℝ, y ^ 3 + y ^ 2 + y - 2 = 0 → y = η) ∧ lambda0 = 2 / η := by
  obtain ⟨h0, h⟩ := lambda0_spec
  refine ⟨2 / lambda0, ?_, ?_, ?_⟩
  · field_simp
    linear_combination (-2) * h
  · intro y hy
    set η := 2 / lambda0 with hη
    have hηe : η ^ 3 + η ^ 2 + η - 2 = 0 := by
      rw [hη]; field_simp; linear_combination (-2) * h
    have hfac : (y - η) * (y ^ 2 + y * η + η ^ 2 + y + η + 1) = 0 := by linear_combination hy - hηe
    rcases mul_eq_zero.mp hfac with e | e
    · linarith
    · nlinarith [sq_nonneg (y + η + 2 / 3), sq_nonneg (y - η)]
  · field_simp

/-- p. 29: `λ_0` is the spectral radius of `M`: it is an eigenvalue of `M` over `ℂ`, and every
eigenvalue has modulus at most `λ_0`. -/
theorem spectrum_matrixM : (lambda0 : ℂ) ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)) ∧
    ∀ z ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)), ‖z‖ ≤ lambda0 := by
  have hcp : (matrixM.map (Nat.cast : ℕ → ℂ)).charpoly =
      Polynomial.X ^ 3 - Polynomial.X ^ 2 - 2 * Polynomial.X - 4 := by
    have e : matrixM.map (Nat.cast : ℕ → ℂ) =
        (matrixM.map (Nat.cast : ℕ → ℤ)).map (Int.castRingHom ℂ) := by
      ext i j; simp
    rw [e, Matrix.charpoly_map, charpoly_matrixM]
    simp
  have hmem : ∀ z : ℂ, z ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)) ↔
      z ^ 3 - z ^ 2 - 2 * z - 4 = 0 := by
    intro z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hcp]
    simp [Polynomial.IsRoot.def]
  obtain ⟨-, h⟩ := lambda0_spec
  refine ⟨(hmem _).mpr ?_, fun z hz => norm_root_le z ((hmem z).mp hz)⟩
  exact_mod_cast h

end ConstantsDev

end ErschlerZheng
end

section
open ErschlerZheng
open ConstantsDev in
theorem solution :
    (∃! x : ℝ, 0 < x ∧ x ^ 3 - x ^ 2 - 2 * x - 4 = 0) ∧
      (0 < lambda0 ∧ lambda0 ^ 3 - lambda0 ^ 2 - 2 * lambda0 - 4 = 0) ∧
      |alpha0 - 7674 / 10000| < 5 / 100000 ∧
      (matrixM.map (Nat.cast : ℕ → ℤ)).charpoly =
        Polynomial.X ^ 3 - Polynomial.X ^ 2 - 2 * Polynomial.X - 4 ∧
      (∀ z : ℂ, z ^ 3 - z ^ 2 - 2 * z - 4 = 0 → ‖z‖ ≤ lambda0) ∧
      ((lambda0 : ℂ) ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)) ∧
        ∀ z ∈ spectrum ℂ (matrixM.map (Nat.cast : ℕ → ℂ)), ‖z‖ ≤ lambda0) ∧
      ∃ η : ℝ, η ^ 3 + η ^ 2 + η - 2 = 0 ∧ (∀ y : ℝ, y ^ 3 + y ^ 2 + y - 2 = 0 → y = η) ∧
        lambda0 = 2 / η := by
  obtain ⟨x, hx, hfx⟩ := exists_root
  refine ⟨⟨x, ⟨hx, hfx⟩, fun y ⟨hy, hfy⟩ => root_unique hy hx hfy hfx⟩, lambda0_spec,
    alpha0_approx, charpoly_matrixM, norm_root_le, spectrum_matrixM, eta_spec⟩
end
