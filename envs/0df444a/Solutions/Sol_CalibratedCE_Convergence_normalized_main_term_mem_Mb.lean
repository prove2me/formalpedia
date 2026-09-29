-- Prove2me | solution 1 for CalibratedCE.Convergence.normalized_main_term_mem_Mb
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:27:12.418238+00:00
-- url     : https://prove2.me/submissions/1c71e273-e825-4e11-afdf-c2b5e12f9a13

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Convergence_BestReply

namespace CalibratedCE.Convergence

theorem aux_nmtm_swap {n : ℕ} (S : Finset (Fin n → ℝ)) (w : (Fin n → ℝ) → ℝ) (W : ℝ)
    (c : Fin n → ℝ) :
    ∑ b, (∑ p ∈ S, p b * w p / W) * c b = (∑ p ∈ S, w p * ∑ b, p b * c b) / W := by
  simp_rw [Finset.sum_div, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

end CalibratedCE.Convergence

open CalibratedCE CalibratedCE.Convergence

theorem solution {m n : ℕ} (u₁ : Fin m → Fin n → ℝ)
    (R₁ : (Fin n → ℝ) → Fin m) (hR₁ : IsBestReply₁ u₁ R₁)
    (f₁ : ℕ → Fin n → ℝ) (hf₁ : ∀ s, IsDist (f₁ s)) (t : ℕ) (a : Fin m)
    (hpos : 0 < ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
      (Shared.N f₁ q t : ℝ)) :
    (fun b => ∑ p ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a),
        p b * (Shared.N f₁ p t : ℝ) /
          ∑ q ∈ ((Finset.range t).image f₁).filter (fun p => R₁ p = a), (Shared.N f₁ q t : ℝ))
      ∈ Mb u₁ a := by
  set S := ((Finset.range t).image f₁).filter (fun p => R₁ p = a) with hS
  set W := ∑ q ∈ S, (CalibratedCE.Shared.N f₁ q t : ℝ) with hW
  have hmem : ∀ p ∈ S, IsDist p ∧ R₁ p = a := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_image] at hp
    obtain ⟨⟨s, _, rfl⟩, h⟩ := hp
    exact ⟨hf₁ s, h⟩
  refine ⟨⟨fun b => ?_, ?_⟩, fun a' => ?_⟩
  · apply Finset.sum_nonneg
    intro p hp
    apply div_nonneg _ hpos.le
    exact mul_nonneg ((hmem p hp).1.1 b) (Nat.cast_nonneg _)
  · have h := aux_nmtm_swap S (fun p => (CalibratedCE.Shared.N f₁ p t : ℝ)) W (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    rw [div_eq_one_iff_eq hpos.ne']
    rw [hW]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [(hmem p hp).1.2, mul_one]
  · rw [aux_nmtm_swap S (fun p => (CalibratedCE.Shared.N f₁ p t : ℝ)) W (fun b => u₁ a' b),
      aux_nmtm_swap S (fun p => (CalibratedCE.Shared.N f₁ p t : ℝ)) W (fun b => u₁ a b)]
    apply div_le_div_of_nonneg_right _ hpos.le
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have := hR₁ p (hmem p hp).1 a'
    rwa [(hmem p hp).2] at this
