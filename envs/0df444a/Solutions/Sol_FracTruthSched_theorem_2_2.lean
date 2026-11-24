-- Prove2me | solution 2 for FracTruthSched.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-24T21:38:39.411328+00:00
-- url     : https://prove2.me/submissions/02843b3e-4987-4333-b4ee-06cdce7c7a04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Theorems.Thm_FracTruthSched_lemma_1
import Theorems.Thm_FracTruthSched_star_bound

set_option autoImplicit false

namespace FTSThm2
open FracTruthSched

/-- The single-machine case: the all-ones input on one task. -/
theorem case_one {n : ℕ} [NeZero n] (hn : n = 1) (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t ∧ 0 < opt t ∧
      (((n : ℝ) + 1) / 2 - δ) * opt t < makespan (R m) t := by
  subst hn
  refine ⟨1, fun _ _ => 1, fun _ _ => zero_le_one, ?_, ?_⟩
  · have : opt (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) = 1 := by
      unfold opt schedMakespan
      simp
    rw [this]; norm_num
  · have hopt : opt (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) = 1 := by
      unfold opt schedMakespan
      simp
    have hx := (hfeas 1 (fun _ _ => 1) (fun _ _ => zero_le_one)).2 0
    have hms : makespan (R 1) (fun _ _ => 1) = 1 := by
      unfold makespan
      simp only [Fin.sum_univ_one] at hx
      simp [hx]
    rw [hopt, hms]; push_cast; linarith

/-- The numerical contradiction: the star bound for all parameters forces `ρ ≥ (n+1)/2`. -/
theorem numeric {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ)
    (H : ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (c : ℚ), 0 < c → c < 1 → ∀ ε : ℝ, 0 < ε →
      1 + (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) ≤
        (((n : ℝ) + 1) / 2 - δ) * (1 + ε)) : False := by
  set ρ : ℝ := ((n : ℝ) + 1) / 2 - δ with hρ
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (n : ℝ) ^ 2 / δ + 2)
  have hNpos : (0 : ℝ) < 3 * (n : ℝ) ^ 2 / δ := by positivity
  have hN2R : (2 : ℝ) ≤ N := by linarith
  have hN2 : 2 ≤ N := by exact_mod_cast hN2R
  have hNpos' : (0 : ℝ) < N := by linarith
  set ε : ℝ := δ / (3 * (|ρ| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hρε : ρ * ε ≤ δ / 3 := by
    have h1 : ρ * ε ≤ |ρ| * ε := mul_le_mul_of_nonneg_right (le_abs_self ρ) hεpos.le
    have h2 : |ρ| * ε ≤ δ / 3 := by
      rw [hε, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg ρ]
    linarith
  have hc0 : (0 : ℚ) < 1 - 1 / (N : ℚ) := by
    have : (1 : ℚ) / N < 1 := by
      rw [div_lt_one (by exact_mod_cast hNpos')]; exact_mod_cast (by omega : 1 < N)
    linarith
  have hc1 : (1 : ℚ) - 1 / (N : ℚ) < 1 := by
    have : (0 : ℚ) < 1 / N := by have : (0:ℚ) < N := by exact_mod_cast hNpos'
                                 positivity
    linarith
  have key := H N hN2 _ hc0 hc1 ε hεpos
  push_cast at key
  -- Bernoulli
  have hq : 1 + ((n - 2 : ℕ) : ℝ) * (-(1 / (N : ℝ))) ≤ (1 + (-(1 / (N : ℝ)))) ^ (n - 2) := by
    apply one_add_mul_le_pow
    have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos']; linarith
    linarith
  rw [Nat.cast_sub hn] at hq
  push_cast at hq
  rw [← sub_eq_add_neg] at hq
  set q := (1 - 1 / (N : ℝ)) ^ (n - 2) with hqdef
  set c : ℝ := 1 - 1 / (N : ℝ) with hcdef
  have hinvN : 1 / (N : ℝ) ≤ δ / (3 * (n : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ hNpos' (by positivity)]
    have : 3 * (n : ℝ) ^ 2 < N * δ := by
      have := (div_lt_iff₀ hδ).1 (by linarith : 3 * (n : ℝ) ^ 2 / δ < N)
      linarith
    linarith
  have hc_nn : 0 ≤ c := by
    have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one hNpos']; linarith
    rw [hcdef]; linarith
  have hcq : c * (1 - ((n : ℝ) - 2) * (1 / N)) ≤ c * q := by
    apply mul_le_mul_of_nonneg_left _ hc_nn; linarith
  have hprod : 1 - ((n : ℝ) - 1) * (1 / N) ≤ c * (1 - ((n : ℝ) - 2) * (1 / N)) := by
    rw [hcdef]
    have : 0 ≤ (1 / (N : ℝ)) * (((n : ℝ) - 2) * (1 / N)) := by
      apply mul_nonneg (by positivity); apply mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hsmall : ((n : ℝ) - 1) / 2 * (((n : ℝ) - 1) * (1 / N)) < δ * (2 / 3) := by
    have h3 : ((n : ℝ) - 1) / 2 * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h4 : ((n : ℝ) - 1) / 2 * (((n : ℝ) - 1) * (1 / N)) ≤ (n : ℝ) ^ 2 * (1 / N) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have h5 : (n : ℝ) ^ 2 * (1 / N) ≤ (n : ℝ) ^ 2 * (δ / (3 * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hinvN (by positivity)
    have h6 : (n : ℝ) ^ 2 * (δ / (3 * (n : ℝ) ^ 2)) = δ / 3 := by
      field_simp
    linarith
  have hA : 0 ≤ ((n : ℝ) - 1) / 2 := by linarith
  have hlow : ((n : ℝ) - 1) / 2 * (1 - ((n : ℝ) - 1) * (1 / N)) ≤ ((n : ℝ) - 1) / 2 * (c * q) :=
    mul_le_mul_of_nonneg_left (hprod.trans hcq) hA
  have hkey : 1 + ((n : ℝ) - 1) / 2 * (c * q) ≤ ρ + ρ * ε := by
    have : c * ((n : ℝ) - 1) / 2 * q = ((n : ℝ) - 1) / 2 * (c * q) := by ring
    rw [← this]; linarith [key]
  nlinarith

end FTSThm2

open FracTruthSched in
theorem solution {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t ∧ 0 < opt t ∧
      (((n : ℝ) + 1) / 2 - δ) * opt t < makespan (R m) t := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n = 1 := by have := NeZero.ne n; omega
    exact FTSThm2.case_one this R hfeas δ hδ
  by_contra hcon
  push Not at hcon
  apply FTSThm2.numeric hn δ hδ
  intro ℓ hℓ c hc0 hc1 ε hε
  obtain ⟨M, hMf, hMt, hload, -, hel, huz, hzti, hsym⟩ :=
    lemma_1 R hfeas htruth _ hcon ℓ hℓ
  obtain ⟨lam, -, h1, h2⟩ :=
    star_bound hn hℓ _ M hMf hMt hel huz hzti hsym hload c hc0 hc1 ε hε
  linarith
