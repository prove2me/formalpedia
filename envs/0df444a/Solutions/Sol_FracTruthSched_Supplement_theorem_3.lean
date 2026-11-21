-- Prove2me | solution 1 for FracTruthSched.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:26:14.509292+00:00
-- url     : https://prove2.me/submissions/9432ef9e-d3bd-4bae-a0b8-fe545082732b

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_makespan
import Definitions.Def_FracTruthSched_disutility
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_C
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasUniqueZeros
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_IsClassSymmetric
import Theorems.Thm_FracTruthSched_star_bound

section
set_option autoImplicit false

namespace FracTruthSched.Dev.T3
open FracTruthSched

lemma n_one (ρ : ℝ) (M : FracMech 1 (CoreTask 1 2))
    (hf : IsFeasibleOn IsGraphInput M)
    (hl : ∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) : 1 ≤ ρ := by
  let t : Fin 1 → CoreTask 1 2 → ℝ := fun _ e => Sum.elim (fun _ => (0:ℝ)) (fun _ => 1) e
  have hg : IsGraphInput t := by
    intro i e
    refine ⟨?_, ?_⟩
    · cases e <;> simp [t]
    · intro hn
      cases e with
      | inl e => simp [t]
      | inr k => exact absurd (Subsingleton.elim _ _) hn
  have hx : M.x t 0 (Sum.inr 0) = 1 := by
    have := (hf t hg).2 (Sum.inr 0)
    simpa using this
  have hm : 1 ≤ makespan M t := by
    unfold makespan
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 1)))
    rw [Fintype.sum_sum_type]
    simp [t, hx]
  have hC : C t ≤ 1 := by
    unfold C
    refine (Finset.inf'_le _ (b := fun _ => (0 : Fin 1)) ?_).trans ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro e
      cases e with
      | inl e => exact absurd e.1.2 (by have h1 := Subsingleton.elim e.1.1.1 e.1.1.2; simp [h1])
      | inr k => exact Subsingleton.elim _ _
    · unfold schedMakespan
      simp [t, Fintype.sum_sum_type]
  have h1 := hl t hg
  have hCn : 0 ≤ C t := by
    unfold C
    refine Finset.le_inf' _ _ ?_
    intro σ _
    unfold schedMakespan
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (0 : Fin 1)))
    exact Finset.sum_nonneg (fun e _ => (hg 0 e).1)
  have hC0 : 0 < C t := by
    rcases hCn.eq_or_lt with h0 | h0
    · rw [← h0] at h1; linarith
    · exact h0
  by_contra hr
  push_neg at hr
  nlinarith

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

end FracTruthSched.Dev.T3

namespace FracTruthSched.Supplement

open FracTruthSched

theorem chk_theorem_3 {n : ℕ} [NeZero n] (ρ : ℝ)
    (h : ∀ ℓ : ℕ, 2 ≤ ℓ → ∃ M : FracMech n (CoreTask n ℓ),
      IsFeasibleOn IsGraphInput M ∧ IsTruthfulOn IsGraphInput M ∧
      IsEligible M ∧ HasUniqueZeros M ∧ HasZeroTypeIrrelevance M ∧ IsClassSymmetric M ∧
      (∀ t, IsGraphInput t → makespan M t ≤ ρ * C t) ∧
      ∀ i : Fin n, ContinuousOn (fun t => disutility M t i) {t | IsGraphInput t}) :
    ((n : ℝ) + 1) / 2 ≤ ρ := by
  have hn0 : n ≠ 0 := NeZero.ne n
  by_cases hn1 : n = 1
  · subst hn1
    obtain ⟨M, hf, -, -, -, -, -, hl, -⟩ := h 2 le_rfl
    have := Dev.T3.n_one ρ M hf hl
    norm_num; linarith
  have hn : 2 ≤ n := by omega
  by_contra hcon
  push_neg at hcon
  obtain ⟨ℓ, c, ε, hℓ, hc0, hc1, hε, hlt⟩ :=
    Dev.T3.analysis n hn (((n : ℝ) + 1) / 2 - ρ) (by linarith) ρ (by ring)
  obtain ⟨M, hf, ht, hel, huz, hzti, hsym, hload, -⟩ := h ℓ hℓ
  obtain ⟨lam, -, h1, h2⟩ := star_bound hn hℓ ρ M hf ht hel huz hzti hsym hload c hc0 hc1 ε hε
  linarith

end FracTruthSched.Supplement
end

theorem solution : type_of% @FracTruthSched.Supplement.chk_theorem_3 := @FracTruthSched.Supplement.chk_theorem_3
