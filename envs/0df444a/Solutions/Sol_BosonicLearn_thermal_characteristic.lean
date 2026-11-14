-- Prove2me | solution 1 for BosonicLearn.thermal_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:42:40.575086+00:00
-- url     : https://prove2.me/submissions/c9083371-a354-40fa-8853-9334c5c90c27

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

noncomputable section

/-- The polynomial `∑_{i ≤ m} C(m,i) yⁱ / i!` (`= Lₘ(-y)`, a Laguerre polynomial). -/
private def Lgen (y : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * y ^ i / (i.factorial : ℝ)

/-- The double series: `H d y (i, m) = dᵐ C(m,i) yⁱ / i!`. -/
private def H (d y : ℝ) (p : ℕ × ℕ) : ℝ :=
  d ^ p.2 * (p.2.choose p.1 : ℝ) * y ^ p.1 / (p.1.factorial : ℝ)

/-- Diagonal entries of the displacement matrix: `D(z)ₘₘ = e^{-|z|²/2} Lₘ(|z|²)`. -/
private lemma disp_diag (z : ℂ) (m : ℕ) :
    displacementMatrix z m m =
      ((Real.exp (-Complex.normSq z / 2) * Lgen (-Complex.normSq z) m : ℝ) : ℂ) := by
  unfold displacementMatrix Lgen
  rw [Nat.min_self, Real.sqrt_mul_self (Nat.cast_nonneg _), ← Finset.sum_flip]
  push_cast
  rw [mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.sub_sub_self hi', Nat.cast_choose ℂ hi']
  have hx : (-(Complex.normSq z : ℂ)) ^ i = z ^ i * (-star z) ^ i := by
    rw [← mul_pow]
    congr 1
    rw [mul_neg, Complex.star_def, Complex.mul_conj]
  rw [hx]
  have h1 : ((i.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (((m - i).factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

/-- Summing the double series over `m` first: negative binomial series. -/
private lemma H_fiber_fst (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) (y : ℝ) (i : ℕ) :
    HasSum (fun m : ℕ => H d y (i, m))
      ((1 - d)⁻¹ * ((y * d / (1 - d)) ^ i / (i.factorial : ℝ))) := by
  have hr : ‖d‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hd0]; exact hd1
  have hne : (1 - d) ≠ 0 := by linarith
  have h0 : ∑ m ∈ Finset.range i, H d y (i, m) = 0 := Finset.sum_eq_zero fun m hm => by
    simp [H, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hm)]
  rw [← hasSum_nat_add_iff' i, h0, sub_zero]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one i hr).mul_left
    (d ^ i * y ^ i / (i.factorial : ℝ))
  have hf : (fun n : ℕ => H d y (i, n + i)) =
      fun n : ℕ => d ^ i * y ^ i / (i.factorial : ℝ) * (((n + i).choose i : ℝ) * d ^ n) := by
    funext n
    simp only [H]
    ring
  have h1 : ((i.factorial : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hv : (1 - d)⁻¹ * ((y * d / (1 - d)) ^ i / (i.factorial : ℝ)) =
      d ^ i * y ^ i / (i.factorial : ℝ) * (1 / (1 - d) ^ (i + 1)) := by
    rw [div_pow, mul_pow, pow_succ]
    field_simp
  rw [hf, hv]
  exact h

/-- Summing the double series over `i` first: a finite sum. -/
private lemma H_fiber_snd (d y : ℝ) (m : ℕ) :
    HasSum (fun i : ℕ => H d y (i, m)) (d ^ m * Lgen y m) := by
  have h : HasSum (fun i : ℕ => H d y (i, m)) (∑ i ∈ Finset.range (m + 1), H d y (i, m)) :=
    hasSum_sum_of_ne_finset_zero (fun i hi => by
      have : m < i := by
        rw [Finset.mem_range] at hi
        omega
      simp [H, Nat.choose_eq_zero_of_lt this])
  have hv : d ^ m * Lgen y m = ∑ i ∈ Finset.range (m + 1), H d y (i, m) := by
    unfold Lgen
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H]
    ring
  rw [hv]
  exact h

private lemma hasSum_real_exp (t : ℝ) :
    HasSum (fun n : ℕ => t ^ n / (n.factorial : ℝ)) (Real.exp t) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp t

private lemma H_nonneg (d : ℝ) (hd0 : 0 ≤ d) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ H d y := by
  intro p
  simp only [H, Pi.zero_apply]
  positivity

private lemma H_summable (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) (y : ℝ) (hy : 0 ≤ y) :
    Summable (H d y) := by
  rw [summable_prod_of_nonneg (H_nonneg d hd0 y hy)]
  refine ⟨fun i => (H_fiber_fst d hd0 hd1 y i).summable, ?_⟩
  have h : (fun i : ℕ => ∑' m, H d y (i, m)) =
      fun i : ℕ => (1 - d)⁻¹ * ((y * d / (1 - d)) ^ i / (i.factorial : ℝ)) :=
    funext fun i => (H_fiber_fst d hd0 hd1 y i).tsum_eq
  rw [h]
  exact (Real.summable_pow_div_factorial _).mul_left _

private lemma H_abs (d : ℝ) (hd0 : 0 ≤ d) (x : ℝ) (hx : 0 ≤ x) (p : ℕ × ℕ) :
    |H d (-x) p| = H d x p := by
  simp only [H, abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hd0, abs_of_nonneg hx,
    Nat.abs_cast]

/-- The generating function of the Laguerre polynomials, with absolute convergence. -/
private lemma real_main (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun m : ℕ => |d ^ m * Lgen (-x) m|) ∧
    HasSum (fun m : ℕ => d ^ m * Lgen (-x) m) ((1 - d)⁻¹ * Real.exp (-x * d / (1 - d))) := by
  have hSx : Summable (H d x) := H_summable d hd0 hd1 x hx
  have hS : Summable (H d (-x)) := by
    refine Summable.of_norm ?_
    simp only [Real.norm_eq_abs, H_abs d hd0 x hx]
    exact hSx
  refine ⟨?_, ?_⟩
  · -- absolute summability
    have hswap : Summable ((H d x) ∘ (Equiv.prodComm ℕ ℕ)) :=
      (Equiv.prodComm ℕ ℕ).summable_iff.mpr hSx
    have hnn : 0 ≤ (H d x) ∘ (Equiv.prodComm ℕ ℕ) :=
      fun p => H_nonneg d hd0 x hx ((Equiv.prodComm ℕ ℕ) p)
    have h2 := ((summable_prod_of_nonneg hnn).mp hswap).2
    have h3 : (fun m : ℕ => ∑' i, ((H d x) ∘ (Equiv.prodComm ℕ ℕ)) (m, i)) =
        fun m : ℕ => d ^ m * Lgen x m :=
      funext fun m => (H_fiber_snd d x m).tsum_eq
    rw [h3] at h2
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_) h2
    rw [abs_mul, abs_pow, abs_of_nonneg hd0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hd0 m)
    unfold Lgen
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hx, Nat.abs_cast]
  · have hH := hS.hasSum
    have h1 := hH.prod_fiberwise (fun i => H_fiber_fst d hd0 hd1 (-x) i)
    have h2 : HasSum (fun i : ℕ => (1 - d)⁻¹ * ((-x * d / (1 - d)) ^ i / (i.factorial : ℝ)))
        ((1 - d)⁻¹ * Real.exp (-x * d / (1 - d))) :=
      (hasSum_real_exp _).mul_left _
    have hval := h1.unique h2
    have hswap : HasSum ((H d (-x)) ∘ (Equiv.prodComm ℕ ℕ)) (∑' p, H d (-x) p) :=
      (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hH
    have h3 := hswap.prod_fiberwise (fun m => H_fiber_snd d (-x) m)
    rw [hval] at h3
    exact h3

theorem solution (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) (z : ℂ) :
    Summable (fun m : ℕ => ‖(d : ℂ) ^ m * displacementMatrix z m m‖) ∧
    HasSum (fun m : ℕ => (d : ℂ) ^ m * displacementMatrix z m m)
      (((1 - d)⁻¹ * Real.exp (-(Complex.normSq z) * (1 + d) / (2 * (1 - d))) : ℝ) : ℂ) := by
  obtain ⟨hsum, hhas⟩ := real_main d hd0 hd1 (Complex.normSq z) (Complex.normSq_nonneg z)
  have key : ∀ m : ℕ, (d : ℂ) ^ m * displacementMatrix z m m =
      ((Real.exp (-Complex.normSq z / 2) * (d ^ m * Lgen (-Complex.normSq z) m) : ℝ) : ℂ) := by
    intro m
    rw [disp_diag]
    push_cast
    ring
  have hne : (1 - d) ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · simp only [key, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    simpa only [abs_mul] using hsum.mul_left (Real.exp (-Complex.normSq z / 2))
  · simp only [key]
    rw [Complex.hasSum_ofReal]
    have h := hhas.mul_left (Real.exp (-Complex.normSq z / 2))
    have hv : (1 - d)⁻¹ * Real.exp (-(Complex.normSq z) * (1 + d) / (2 * (1 - d))) =
        Real.exp (-Complex.normSq z / 2) *
          ((1 - d)⁻¹ * Real.exp (-Complex.normSq z * d / (1 - d))) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [hv]
    exact h
