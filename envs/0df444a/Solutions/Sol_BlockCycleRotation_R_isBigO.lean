-- Prove2me | solution 1 for BlockCycleRotation.R_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:53:27.727039+00:00
-- url     : https://prove2.me/submissions/8759b9e4-57b2-46b9-9c99-6e76508cf6e5

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesQ
import Theorems.Thm_BlockCycleRotation_Q_isBigO
import Theorems.Thm_BlockCycleRotation_moebius_main
import Mathlib

open Finset Real

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem Qquad_eq {n : ℕ} (hn : 0 < n) : Qquad n = ∑ d ∈ n.divisors, Rquad (n / d) := by
  unfold Qquad Rquad
  exact_mod_cast sum_snd_quadruplesQ hn

/-- `Q(n) = ∑_{d ∣ n} R(d)`. -/
theorem sum_Rquad {n : ℕ} (hn : 0 < n) : ∑ d ∈ n.divisors, Rquad d = Qquad n := by
  rw [Qquad_eq hn, Nat.sum_div_divisors]

/-- **Equation (mobius).**  `R(n) = ∑_{d ∣ n} μ(d) · Q(n/d)`. -/
theorem moebius_Rquad {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 • Qquad x.2 = Rquad n :=
  ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq.1 (fun _ hm => sum_Rquad hm) n hn

/-- **The errors sum to at most `d(n)` times their maximum.** -/
theorem sum_divisors_le {n : ℕ} (g : ℕ → ℝ) (K : ℝ)
    (hg : ∀ d ∈ n.divisors, g d ≤ K) :
    ∑ d ∈ n.divisors, g d ≤ (n.divisors.card : ℝ) * K := by
  calc ∑ d ∈ n.divisors, g d ≤ ∑ _d ∈ n.divisors, K := Finset.sum_le_sum hg
    _ = (n.divisors.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]

end BlockCycleRotation

open BlockCycleRotation in
/-- **`R(n) = C·n² + O(n^{3/2+ε})`.** -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Rquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2| ≤ K * (n : ℝ) ^ (3 / 2 + ε):= by
  classical
  obtain ⟨K1, hK1, hQ⟩ := Q_isBigO (half_pos hε)
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le (half_pos hε)
  refine ⟨K1 * C0, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hR : ((Rquad n : ℤ) : ℝ)
      = ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          * ((Qquad (n / d) : ℤ) : ℝ) := by
    have h := moebius_Rquad hn
    rw [Nat.sum_divisorsAntidiagonal
      (fun x y => (ArithmeticFunction.moebius x) • Qquad y)] at h
    rw [← h]
    push_cast [zsmul_eq_mul]
    ring
  have hterm : ∀ d ∈ n.divisors,
      |((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((Qquad (n / d) : ℤ) : ℝ)
        - ((ArithmeticFunction.moebius d : ℤ) : ℝ)
            * (cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2)|
      ≤ K1 * (n : ℝ) ^ (3 / 2 + ε / 2) := by
    intro d hd
    obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
    have hk : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
    have hkn : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.div_le_self n d
    rw [← mul_sub, abs_mul]
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hq := hQ (n / d) hk
    have hmono : ((n / d : ℕ) : ℝ) ^ (3 / 2 + ε / 2) ≤ (n : ℝ) ^ (3 / 2 + ε / 2) :=
      Real.rpow_le_rpow (by positivity) hkn (by linarith)
    have habs : (0 : ℝ) ≤ |((Qquad (n / d) : ℤ) : ℝ)
        - cConst * ((n / d : ℕ) : ℝ) ^ 2 * ∑ e ∈ (n / d).divisors, 1 / (e : ℝ) ^ 2| :=
      abs_nonneg _
    nlinarith [hmu, hq, hmono, habs, hK1, abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]
  rw [hR, ← moebius_main hn, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_divisors_le _ _ hterm).trans ?_
  have hd := hCd n hn.ne'
  have hstep : (n.divisors.card : ℝ) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2))
      ≤ (C0 * (n : ℝ) ^ (ε / 2)) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2)) := by
    refine mul_le_mul_of_nonneg_right hd ?_
    positivity
  refine hstep.trans (le_of_eq ?_)
  have hpow : (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2) = (n : ℝ) ^ (3 / 2 + ε) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  calc (C0 * (n : ℝ) ^ (ε / 2)) * (K1 * (n : ℝ) ^ (3 / 2 + ε / 2))
      = K1 * C0 * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (3 / 2 + ε / 2)) := by ring
    _ = K1 * C0 * (n : ℝ) ^ (3 / 2 + ε) := by rw [hpow]
