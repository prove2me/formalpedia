-- Prove2me | solution 1 for FuchsThesis.Chernoff.eq_2_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T00:08:46.435845+00:00
-- url     : https://prove2.me/submissions/5e833fb3-c697-4724-9189-d91b4f34abad

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_errorProb
import Definitions.Def_FuchsThesis_Chernoff_IsBayesDecision
import Definitions.Def_FuchsThesis_Chernoff_bayesError

open CalibratedCE.Forecast

namespace Aux_Fuchs_211

theorem E1 (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a + c) * (1 - max (a / (a + c)) (c / (a + c))) = min a c := by
  by_cases hs : a + c = 0
  · have ha0 : a = 0 := by linarith
    have hc0 : c = 0 := by linarith
    rw [hs, zero_mul, ha0, hc0, min_self]
  · have hs0 : 0 < a + c := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    rw [mul_sub, mul_one, mul_max_of_nonneg _ _ hs0.le, mul_div_cancel₀ _ hs,
      mul_div_cancel₀ _ hs]
    rcases le_total a c with h | h
    · rw [max_eq_right h, min_eq_left h]
      ring
    · rw [max_eq_left h, min_eq_right h]
      ring

theorem E2 (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (a + c) * min (a / (a + c)) (c / (a + c)) = min a c := by
  by_cases hs : a + c = 0
  · have ha0 : a = 0 := by linarith
    have hc0 : c = 0 := by linarith
    rw [hs, zero_mul, ha0, hc0, min_self]
  · have hs0 : 0 < a + c := lt_of_le_of_ne (by linarith) (Ne.symm hs)
    rw [mul_min_of_nonneg _ _ hs0.le, mul_div_cancel₀ _ hs, mul_div_cancel₀ _ hs]

theorem T (a c d : ℝ) (hd : d = 0 ∨ d = 1) (h0 : c < a → d = 0) (h1 : a < c → d = 1) :
    d * a + (1 - d) * c = min a c := by
  rcases hd with rfl | rfl
  · have : ¬ a < c := fun hac => by
      have := h1 hac
      norm_num at this
    rw [min_eq_right (not_lt.1 this)]
    ring
  · have : ¬ c < a := fun hca => by
      have := h0 hca
      norm_num at this
    rw [min_eq_left (not_lt.1 this)]
    ring

end Aux_Fuchs_211

open FuchsThesis.Chernoff in
theorem solution {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (δB : B → Fin 2) (hB : IsBayesDecision π0 π1 p0 p1 δB) :
    errorProb π0 π1 p0 p1 δB =
        ∑ b, (π0 * p0 b + π1 * p1 b) *
          (1 - max (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
                   (π1 * p1 b / (π0 * p0 b + π1 * p1 b))) ∧
      ∑ b, (π0 * p0 b + π1 * p1 b) *
          (1 - max (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
                   (π1 * p1 b / (π0 * p0 b + π1 * p1 b))) =
        ∑ b, (π0 * p0 b + π1 * p1 b) *
          min (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
              (π1 * p1 b / (π0 * p0 b + π1 * p1 b)) ∧
      ∑ b, (π0 * p0 b + π1 * p1 b) *
          min (π0 * p0 b / (π0 * p0 b + π1 * p1 b))
              (π1 * p1 b / (π0 * p0 b + π1 * p1 b)) =
        bayesError π0 π1 p0 p1 := by
  have ha : ∀ b, 0 ≤ π0 * p0 b := fun b => mul_nonneg hπ0 (hp0.1 b)
  have hc : ∀ b, 0 ≤ π1 * p1 b := fun b => mul_nonneg hπ1 (hp1.1 b)
  have herr : errorProb π0 π1 p0 p1 δB = ∑ b, (((δB b : ℕ) : ℝ) * (π0 * p0 b) +
      (1 - ((δB b : ℕ) : ℝ)) * (π1 * p1 b)) := by
    unfold errorProb
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have hT : ∀ b, ((δB b : ℕ) : ℝ) * (π0 * p0 b) + (1 - ((δB b : ℕ) : ℝ)) * (π1 * p1 b) =
      min (π0 * p0 b) (π1 * p1 b) := by
    intro b
    apply Aux_Fuchs_211.T
    · have hlt := (δB b).isLt
      have h01 : (δB b : ℕ) = 0 ∨ (δB b : ℕ) = 1 := by omega
      rcases h01 with h | h
      · left; rw [h]; norm_num
      · right; rw [h]; norm_num
    · intro hlt
      rw [(hB b).1 hlt]
      simp
    · intro hlt
      rw [(hB b).2 hlt]
      simp
  refine ⟨?_, ?_, ?_⟩
  · rw [herr]
    exact Finset.sum_congr rfl (fun b _ => by rw [hT b, Aux_Fuchs_211.E1 _ _ (ha b) (hc b)])
  · exact Finset.sum_congr rfl (fun b _ => by
      rw [Aux_Fuchs_211.E1 _ _ (ha b) (hc b), Aux_Fuchs_211.E2 _ _ (ha b) (hc b)])
  · unfold bayesError
    exact Finset.sum_congr rfl (fun b _ => Aux_Fuchs_211.E2 _ _ (ha b) (hc b))
