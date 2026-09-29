-- Prove2me | solution 1 for CalibratedCE.Generic.CE_condForecast_best_response
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:16:14.860447+00:00
-- url     : https://prove2.me/submissions/46341283-0d48-45ac-8948-1943fb247d30

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

namespace CalibratedCE.Generic

theorem aux_cecf_row {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) (a a' : Fin m) :
    ∑ b, D a b * u₁ a' b ≤ ∑ b, D a b * u₁ a b := by
  have h := hCE.2.1 (Function.update id a a')
  have key : ∑ x, ∑ b, D x b * u₁ (Function.update id a a' x) b
      - ∑ x, ∑ b, D x b * u₁ x b = ∑ b, D a b * u₁ a' b - ∑ b, D a b * u₁ a b := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · simp
    · intro x _ hx
      rw [Function.update_of_ne hx]
      simp
    · intro h; exact absurd (Finset.mem_univ a) h
  linarith

theorem aux_cecf_col {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) (b b' : Fin n) :
    ∑ a, D a b * u₂ a b' ≤ ∑ a, D a b * u₂ a b := by
  have h := hCE.2.2 (Function.update id b b')
  rw [Finset.sum_comm (f := fun a b_1 => D a b_1 * u₂ a (Function.update id b b' b_1)),
    Finset.sum_comm (f := fun a b_1 => D a b_1 * u₂ a b_1)] at h
  have key : ∑ y, ∑ x, D x y * u₂ x (Function.update id b b' y)
      - ∑ y, ∑ x, D x y * u₂ x y = ∑ a, D a b * u₂ a b' - ∑ a, D a b * u₂ a b := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      rw [Function.update_of_ne hy]
      simp
    · intro h; exact absurd (Finset.mem_univ b) h
  linarith

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ)
    (D : Fin m → Fin n → ℝ) (hCE : IsCE u₁ u₂ D) :
    (∀ a, 0 < ∑ c, D a c → condForecast₁ D a ∈ Mb u₁ a) ∧
      (∀ b, 0 < ∑ c, D c b → ∀ b',
        ∑ a, condForecast₂ D b a * u₂ a b' ≤ ∑ a, condForecast₂ D b a * u₂ a b) := by
  refine ⟨fun a ha => ?_, fun b hb b' => ?_⟩
  · refine ⟨⟨fun c => ?_, ?_⟩, fun a' => ?_⟩
    · exact div_nonneg (hCE.1.1 a c) ha.le
    · simp only [condForecast₁]
      rw [← Finset.sum_div, div_self ha.ne']
    · simp only [condForecast₁, div_mul_eq_mul_div]
      rw [← Finset.sum_div, ← Finset.sum_div]
      exact div_le_div_of_nonneg_right (aux_cecf_row u₁ u₂ D hCE a a') ha.le
  · simp only [condForecast₂, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (aux_cecf_col u₁ u₂ D hCE b b') hb.le
