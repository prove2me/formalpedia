-- Prove2me | solution 1 for FracTruthSched.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:09:15.171199+00:00
-- url     : https://prove2.me/submissions/3cab1bdf-e174-41e1-ab60-abd619e26d55

import Mathlib
import Definitions.Def_FracTruthSched_Nonneg
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_opt
import Theorems.Thm_FracTruthSched_lemma_1
import Theorems.Thm_FracTruthSched_star_bound

section
set_option autoImplicit false

namespace FracTruthSched.Dev.T2
open FracTruthSched

lemma n_one (R : (m : ℕ) → FracMech 1 (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin 1 → Fin m → ℝ), Nonneg t ∧ 0 < opt t ∧
      ((((1 : ℕ) : ℝ) + 1) / 2 - δ) * opt t < makespan (R m) t := by
  refine ⟨1, fun _ _ => 1, fun _ _ => zero_le_one, ?_⟩
  have ho : opt (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) = 1 := by
    unfold opt schedMakespan
    simp
  have hx : (R 1).x (fun _ _ => 1) 0 0 = 1 := by
    have := (hfeas 1 (fun _ _ => 1) (fun _ _ => zero_le_one)).2 0
    simpa using this
  have hm : makespan (R 1) (fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ)) = 1 := by
    unfold makespan; simp [hx]
  rw [ho, hm]
  refine ⟨one_pos, ?_⟩
  norm_num; linarith

lemma analysis (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) (ρ : ℝ) (hρ : ρ = ((n : ℝ) + 1) / 2 - δ) :
    ∃ (ℓ : ℕ) (c : ℚ) (ε : ℝ), 2 ≤ ℓ ∧ 0 < c ∧ c < 1 ∧ 0 < ε ∧
      ρ * (1 + ε) < 1 + (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set η : ℝ := min (δ / (4 * n)) (1 / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hη2 : (n - 1 : ℝ) * η ≤ δ / 4 := by
    have : η ≤ δ / (4 * n) := min_le_left _ _
    calc (n - 1 : ℝ) * η ≤ n * (δ / (4 * n)) := by
          apply mul_le_mul (by linarith) this hη0.le (by linarith)
      _ = δ / 4 := by field_simp
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (show (max 0 (1 - η) : ℝ) < 1 from
    max_lt zero_lt_one (by linarith))
  obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) / η)
  set ℓ : ℕ := max 2 N with hℓ
  have hℓ2 : 2 ≤ ℓ := le_max_left _ _
  have hℓN : (N : ℝ) ≤ ℓ := by exact_mod_cast le_max_right 2 N
  have hℓpos : (0 : ℝ) < ℓ := by have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
                                 linarith
  set ε : ℝ := min 1 (δ / (4 * ((n : ℝ) + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hεδ : ((n : ℝ) + 1) / 2 * ε ≤ δ / 8 := by
    have : ε ≤ δ / (4 * ((n : ℝ) + 1)) := min_le_right _ _
    calc ((n : ℝ) + 1) / 2 * ε ≤ ((n : ℝ) + 1) / 2 * (δ / (4 * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ / 8 := by field_simp; ring
  refine ⟨ℓ, c, ε, hℓ2, ?_, ?_, hε0, ?_⟩
  · have : (0 : ℝ) < c := lt_of_le_of_lt (le_max_left _ _) hc1
    exact_mod_cast this
  · exact_mod_cast hc2
  · have hc0 : (1 - η : ℝ) < c := lt_of_le_of_lt (le_max_right _ _) hc1
    have hnℓ : ((n - 2 : ℕ) : ℝ) / ℓ < η := by
      rw [div_lt_iff₀ hℓpos]
      have : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
      have h2 : (n : ℝ) < η * N := by
        rw [div_lt_iff₀ hη0] at hN; linarith
      nlinarith
    have hbern : 1 + ((n - 2 : ℕ) : ℝ) * (-(1 / (ℓ : ℝ))) ≤ (1 + -(1 / (ℓ : ℝ))) ^ (n - 2) :=
      one_add_mul_le_pow (by
        have : 0 < 1 / (ℓ : ℝ) := by positivity
        have : 1 / (ℓ : ℝ) ≤ 1 := by
          rw [div_le_one hℓpos]; exact_mod_cast (by omega : 1 ≤ ℓ)
        linarith) _
    have hb : 1 - η < (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
      have : 1 + ((n - 2 : ℕ) : ℝ) * (-(1 / (ℓ : ℝ))) = 1 - ((n - 2 : ℕ) : ℝ) / ℓ := by ring
      rw [this] at hbern
      have e2 : (1 + -(1 / (ℓ : ℝ))) = 1 - 1 / (ℓ : ℝ) := by ring
      rw [e2] at hbern
      linarith
    have hcp : 1 - 2 * η ≤ (c : ℝ) * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
      nlinarith
    have hA : 0 ≤ ((n : ℝ) - 1) / 2 := by linarith
    have hL : 1 + ((n : ℝ) - 1) / 2 * (1 - 2 * η) ≤
        1 + (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
      have := mul_le_mul_of_nonneg_left hcp hA
      nlinarith
    by_cases hρ0 : ρ ≤ 0
    · have : ρ * (1 + ε) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hρ0 (by linarith)
      have hpos : 0 ≤ (c : ℝ) * ((n : ℝ) - 1) / 2 * (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
        have : 0 < (c : ℝ) := lt_of_le_of_lt (le_max_left _ _) hc1
        have h1 : 0 ≤ (1 - 1 / (ℓ : ℝ)) ^ (n - 2) := by
          apply pow_nonneg
          have : 1 / (ℓ : ℝ) ≤ 1 := by
            rw [div_le_one hℓpos]; exact_mod_cast (by omega : 1 ≤ ℓ)
          linarith
        have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
        exact mul_nonneg (div_nonneg (mul_nonneg this.le hn1) (by norm_num)) h1
      linarith
    · have hρ0 := not_le.mp hρ0
      have h1 : ρ * (1 + ε) = ρ + ρ * ε := by ring
      have h2 : ρ * ε ≤ ((n : ℝ) + 1) / 2 * ε :=
        mul_le_mul_of_nonneg_right (by rw [hρ]; linarith) hε0.le
      nlinarith

end FracTruthSched.Dev.T2

namespace FracTruthSched

theorem chk_theorem_2 {n : ℕ} [NeZero n] (R : (m : ℕ) → FracMech n (Fin m))
    (hfeas : ∀ m, IsFeasibleOn Nonneg (R m)) (htruth : ∀ m, IsTruthfulOn Nonneg (R m))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t ∧ 0 < opt t ∧
      (((n : ℝ) + 1) / 2 - δ) * opt t < makespan (R m) t := by
  have hn0 : n ≠ 0 := NeZero.ne n
  by_cases hn1 : n = 1
  · subst hn1
    exact Dev.T2.n_one R hfeas δ hδ
  have hn : 2 ≤ n := by omega
  by_contra hcon
  push_neg at hcon
  have hρ : ∀ (m : ℕ) (t : Fin n → Fin m → ℝ), Nonneg t → 0 < opt t →
      makespan (R m) t ≤ (((n : ℝ) + 1) / 2 - δ) * opt t :=
    fun m t h1 h2 => hcon m t h1 h2
  obtain ⟨ℓ, c, ε, hℓ, hc0, hc1, hε, hlt⟩ :=
    Dev.T2.analysis n hn δ hδ _ rfl
  obtain ⟨M, hMf, hMt, hMload, -, hel, huz, hzti, hsym⟩ :=
    lemma_1 R hfeas htruth (((n : ℝ) + 1) / 2 - δ) hρ ℓ hℓ
  obtain ⟨lam, -, h1, h2⟩ := star_bound hn hℓ _ M hMf hMt hel huz hzti hsym hMload c hc0 hc1 ε hε
  linarith

end FracTruthSched
end

theorem solution : type_of% @FracTruthSched.chk_theorem_2 := @FracTruthSched.chk_theorem_2
