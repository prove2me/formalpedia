-- Prove2me | solution 1 for BookProof.ChapterE.exists_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:27:33.352374+00:00
-- url     : https://prove2.me/submissions/168b494e-33ac-42f8-9dde-6425e2f5078c

-- Generated from ChapterE.lean — solution of BookProof.ChapterE.exists_uniformizer
import Mathlib
import Definitions.Def_ChapterE
open BookProof.ChapterE



open scoped Matrix BigOperators
open Filter
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ ∀ i j, ‖U i j‖ ^ 2 = 1 / n := by

  have hn0 : n ≠ 0 := by omega
  let U : Matrix (Fin n) (Fin n) ℂ := fun i j =>
      Complex.exp (2 * Real.pi * Complex.I * i.val * j.val / n) / Real.sqrt n
  have hUent : ∀ a b : Fin n, U a b =
      Complex.exp (2 * Real.pi * Complex.I * a.val * b.val / n) / Real.sqrt n := fun _ _ => rfl
  refine ⟨U, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, hUent]
    have hn0c : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hterm : ∀ x : Fin n,
        star (Complex.exp (2 * Real.pi * Complex.I * x.val * i.val / n) / Real.sqrt n) *
          (Complex.exp (2 * Real.pi * Complex.I * x.val * j.val / n) / Real.sqrt n)
        = (n : ℂ)⁻¹ *
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) := by
      intro x
      rw [star_div₀, Complex.star_def, ← Complex.exp_conj, Complex.conj_ofReal]
      have hsa : star (2 * Real.pi * Complex.I * x.val * i.val / n)
          = -(2 * Real.pi * Complex.I * x.val * i.val / n) := by
        simp [star_mul, star_div₀, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [Complex.star_def] at hsa
      rw [hsa, div_mul_div_comm, ← Complex.exp_add]
      have hs2 : ((Real.sqrt n : ℝ) : ℂ) * Real.sqrt n = (n : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : 0 ≤ (n : ℝ))]
        rfl
      rw [hs2]
      rw [show -((2 * Real.pi * Complex.I * x.val * i.val) / n)
              + (2 * Real.pi * Complex.I * x.val * j.val / n)
            = 2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n by ring]
      rw [div_eq_mul_inv, mul_comm]
    rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
    by_cases hij : i = j
    · rw [if_pos hij]
      have h0 : ∑ x : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = (n : ℂ) := by
        have hterm0 : ∀ x : Fin n,
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = 1 := by
          intro x
          rw [show (j.val - i.val : ℂ) = 0 from by rw [hij]; ring, mul_zero, zero_div,
            Complex.exp_zero]
        rw [Finset.sum_congr rfl (fun x _ => hterm0 x), Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, Nat.smul_one_eq_cast]
      rw [h0, mul_comm, mul_inv_cancel₀ hn0c]
    · rw [if_neg hij]
      have hne : Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ≠ 1 := by
        intro h
        obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
        rw [← mul_div_assoc'] at hk
        rw [show ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
              = (2 * Real.pi * Complex.I) * ((k : ℤ) : ℂ) from by ring] at hk
        have h2 : (j.val - i.val : ℂ) / (n : ℂ) = ((k : ℤ) : ℂ) :=
          mul_left_cancel₀ Complex.two_pi_I_ne_zero hk
        have h4 : (j.val - i.val : ℂ) = ((k : ℤ) : ℂ) * (n : ℂ) := by
          rw [← div_eq_iff hn0c]
          exact h2
        have hr : ((k * (n : ℤ)) : ℂ) = ((k : ℤ) : ℂ) * (n : ℂ) := by norm_cast
        have hl : (((j.val : ℤ) - (i.val : ℤ)) : ℂ) = (j.val - i.val : ℂ) := by norm_cast
        have h5 : (((j.val : ℤ) - (i.val : ℤ)) : ℂ) = ((k * (n : ℤ)) : ℂ) := by
          rw [hl, h4, hr]
        have h4' : ((j.val : ℤ) - (i.val : ℤ)) = k * (n : ℤ) := by exact_mod_cast h5
        have hi : i.val < n := Fin.is_lt i
        have hj : j.val < n := Fin.is_lt j
        have hij' : i.val ≠ j.val := fun hh => hij (Fin.ext hh)
        by_cases hk0 : k = 0
        · rw [hk0, zero_mul] at h4'
          omega
        · have hz : (0 : ℤ) < |k| := abs_pos.mpr hk0
          have hz1 : (1 : ℤ) ≤ |k| := by omega
          have hn0z : (0 : ℤ) < n := by omega
          have hle1 : (n : ℤ) ≤ |k| * n := by nlinarith [hz1, hn0z]
          have h8 : |k| * n = |(j.val : ℤ) - (i.val : ℤ)| := by
            rw [h4', abs_mul, abs_of_nonneg (by omega : (0 : ℤ) ≤ n)]
          have hb : |(j.val : ℤ) - (i.val : ℤ)| ≤ (n : ℤ) - 1 := by
            apply abs_le.mpr
            constructor <;> omega
          have hcon : (n : ℤ) ≤ (n : ℤ) - 1 :=
            le_trans hle1 (le_trans (le_of_eq h8) hb)
          omega
      have hpow : Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ^ n = 1 := by
        rw [← Complex.exp_nat_mul, mul_div_assoc', mul_div_cancel_left₀ _ hn0c]
        refine Complex.exp_eq_one_iff.mpr ⟨(j.val : ℤ) - i.val, ?_⟩
        rw [show (j.val - i.val : ℂ) = (((j.val : ℤ) - i.val : ℤ) : ℂ) from by norm_cast]
        ring
      have hsum : ∑ x : Fin n,
          Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n) = 0 := by
        have hterm_pow : ∀ x : Fin n,
            Complex.exp (2 * Real.pi * Complex.I * x.val * (j.val - i.val) / n)
              = Complex.exp (2 * Real.pi * Complex.I * (j.val - i.val) / n) ^ x.val := by
          intro x
          rw [← Complex.exp_nat_mul]
          ring_nf
        rw [Finset.sum_congr rfl (fun x _ => hterm_pow x), ← Finset.sum_range,
          geom_sum_eq hne, hpow, sub_self, zero_div]
      rw [hsum, mul_zero]
  · intro i j
    rw [hUent]
    norm_num [Complex.norm_exp]
