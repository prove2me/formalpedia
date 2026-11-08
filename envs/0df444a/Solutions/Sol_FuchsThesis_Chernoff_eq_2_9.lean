-- Prove2me | solution 1 for FuchsThesis.Chernoff.eq_2_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:16:21.615163+00:00
-- url     : https://prove2.me/submissions/7928095f-73fe-4002-923f-e9104b6d3693

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_errorProb
import Definitions.Def_FuchsThesis_Chernoff_IsBayesDecision

open CalibratedCE.Forecast

open FuchsThesis.Chernoff in
theorem solution {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (δB : B → Fin 2) (hB : IsBayesDecision π0 π1 p0 p1 δB) (δ : B → Fin 2) :
    errorProb π0 π1 p0 p1 δB ≤ errorProb π0 π1 p0 p1 δ ∧
      (¬ IsBayesDecision π0 π1 p0 p1 δ →
        errorProb π0 π1 p0 p1 δB < errorProb π0 π1 p0 p1 δ) := by
  have hrw : ∀ δ' : B → Fin 2, errorProb π0 π1 p0 p1 δ' =
      ∑ b, (π0 * ((δ' b : ℕ) : ℝ) * p0 b + π1 * (1 - ((δ' b : ℕ) : ℝ)) * p1 b) := by
    intro δ'
    unfold errorProb
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hval : ∀ (k : Fin 2) (b : B),
      π0 * ((k : ℕ) : ℝ) * p0 b + π1 * (1 - ((k : ℕ) : ℝ)) * p1 b =
        if k = 0 then π1 * p1 b else π0 * p0 b := by
    intro k b
    fin_cases k <;> simp
  have hle : ∀ b, π0 * ((δB b : ℕ) : ℝ) * p0 b + π1 * (1 - ((δB b : ℕ) : ℝ)) * p1 b ≤
      π0 * ((δ b : ℕ) : ℝ) * p0 b + π1 * (1 - ((δ b : ℕ) : ℝ)) * p1 b := by
    intro b
    rw [hval, hval]
    rcases lt_trichotomy (π1 * p1 b) (π0 * p0 b) with h | h | h
    · rw [if_pos ((hB b).1 h)]
      split_ifs <;> linarith
    · split_ifs <;> linarith
    · have h1 := (hB b).2 h
      rw [if_neg (by rw [h1]; decide)]
      split_ifs <;> linarith
  refine ⟨?_, fun hnot => ?_⟩
  · rw [hrw, hrw]
    exact Finset.sum_le_sum fun b _ => hle b
  · rw [hrw, hrw]
    obtain ⟨b, hb⟩ := not_forall.mp hnot
    apply Finset.sum_lt_sum (fun b _ => hle b)
    refine ⟨b, Finset.mem_univ b, ?_⟩
    rw [hval, hval]
    rcases not_and_or.mp hb with hb | hb
    · obtain ⟨h, hδ⟩ := _root_.not_imp.mp hb
      rw [if_pos ((hB b).1 h), if_neg hδ]
      exact h
    · obtain ⟨h, hδ⟩ := _root_.not_imp.mp hb
      have h1 := (hB b).2 h
      have h0 : δ b = 0 := by
        generalize δ b = k at hδ ⊢
        fin_cases k
        · rfl
        · exact absurd rfl hδ
      rw [if_neg (by rw [h1]; decide), if_pos h0]
      exact h
