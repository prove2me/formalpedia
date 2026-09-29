-- Prove2me | solution 1 for CalibratedCE.Generic.pert_strict_best_reply
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:31:53.726638+00:00
-- url     : https://prove2.me/submissions/049089fc-9b93-42e2-96ea-80ac820e02d3

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Generic_Forecasts

open Filter Topology

namespace CalibratedCE.Generic

theorem aux_psbr_sum_expand {n : ℕ} (pstar q v : Fin n → ℝ) (i : ℕ) :
    ∑ b, pert pstar q i b * v b
      = (1 - 1 / (i : ℝ)) * ∑ b, pstar b * v b + (1 / (i : ℝ)) * ∑ b, q b * v b := by
  simp only [pert, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m)
    (pstar q : Fin n → ℝ) (hpstar : pstar ∈ Mb u₁ a) (hq : IsDist q)
    (hqa : ∀ a', a' ≠ a → ∑ b, q b * u₁ a' b < ∑ b, q b * u₁ a b) :
    (∀ i : ℕ, 1 ≤ i → IsDist (pert pstar q i) ∧
        ∀ a', a' ≠ a → ∑ b, pert pstar q i b * u₁ a' b < ∑ b, pert pstar q i b * u₁ a b) ∧
      Tendsto (pert pstar q) atTop (𝓝 pstar) := by
  obtain ⟨⟨hp0, hp1⟩, hpbr⟩ := hpstar
  obtain ⟨hq0, hq1⟩ := hq
  refine ⟨fun i hi => ?_, ?_⟩
  · have hipos : (0 : ℝ) < i := by exact_mod_cast hi
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    have ht0 : (0 : ℝ) < 1 / (i : ℝ) := by positivity
    have ht1 : 1 / (i : ℝ) ≤ 1 := by
      rw [div_le_one hipos]; exact hi1
    have hs0 : (0 : ℝ) ≤ 1 - 1 / (i : ℝ) := by linarith
    refine ⟨⟨fun b => ?_, ?_⟩, fun a' ha' => ?_⟩
    · simp only [pert]
      have := hp0 b
      have := hq0 b
      positivity
    · have := aux_psbr_sum_expand pstar q (fun _ => (1 : ℝ)) i
      simp only [mul_one] at this
      rw [this, hp1, hq1]
      ring
    · rw [aux_psbr_sum_expand, aux_psbr_sum_expand]
      have h1 := mul_le_mul_of_nonneg_left (hpbr a') hs0
      have h2 := mul_lt_mul_of_pos_left (hqa a' ha') ht0
      linarith
  · rw [tendsto_pi_nhds]
    intro b
    have ht := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h : Tendsto (fun i : ℕ => (1 - 1 / (i : ℝ)) * pstar b + (1 / (i : ℝ)) * q b)
        atTop (𝓝 ((1 - 0) * pstar b + 0 * q b)) :=
      ((tendsto_const_nhds.sub ht).mul tendsto_const_nhds).add (ht.mul tendsto_const_nhds)
    simp only [sub_zero, one_mul, zero_mul, add_zero] at h
    exact h
