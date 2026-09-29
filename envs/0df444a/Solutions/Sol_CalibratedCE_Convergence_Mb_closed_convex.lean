-- Prove2me | solution 1 for CalibratedCE.Convergence.Mb_closed_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:19.778182+00:00
-- url     : https://prove2.me/submissions/39327be8-16da-4c0a-afcd-15f6b0b6ebb3

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Convergence_BestReply

open CalibratedCE.Convergence

theorem solution {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (a : Fin m) :
    IsClosed (Mb u₁ a) ∧ Convex ℝ (Mb u₁ a) := by
  constructor
  · -- `Mb` is cut out by finitely many (closed) linear conditions
    have hset : Mb u₁ a =
        (⋂ b : Fin n, {p : Fin n → ℝ | 0 ≤ p b}) ∩
          {p : Fin n → ℝ | ∑ b, p b = 1} ∩
          (⋂ a' : Fin m, {p : Fin n → ℝ | ∑ b, p b * u₁ a' b ≤ ∑ b, p b * u₁ a b}) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hnn, hs⟩, hbr⟩
        exact ⟨⟨fun b => hnn b, hs⟩, fun a' => hbr a'⟩
      · rintro ⟨⟨hnn, hs⟩, hbr⟩
        exact ⟨⟨fun b => hnn b, hs⟩, fun a' => hbr a'⟩
    rw [hset]
    have hlin : ∀ c : Fin n → ℝ, Continuous fun p : Fin n → ℝ => ∑ b, p b * c b := by
      intro c
      exact continuous_finset_sum _ fun b _ => (continuous_apply b).mul continuous_const
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · exact isClosed_iInter fun b => isClosed_le continuous_const (continuous_apply b)
    · exact isClosed_eq (continuous_finset_sum _ fun b _ => continuous_apply b) continuous_const
    · exact isClosed_iInter fun a' => isClosed_le (hlin _) (hlin _)
  · intro p hp q hq s t hs ht hst
    obtain ⟨⟨hpnn, hps⟩, hpbr⟩ := hp
    obtain ⟨⟨hqnn, hqs⟩, hqbr⟩ := hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro b
      have : (s • p + t • q) b = s * p b + t * q b := by simp [Pi.add_apply, Pi.smul_apply]
      rw [this]
      have h1 : 0 ≤ s * p b := mul_nonneg hs (hpnn b)
      have h2 : 0 ≤ t * q b := mul_nonneg ht (hqnn b)
      linarith
    · have hexp : ∑ b, (s • p + t • q) b = s * (∑ b, p b) + t * (∑ b, q b) := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
      rw [hexp, hps, hqs]
      linarith
    · intro a'
      have hexp : ∀ c : Fin n → ℝ, ∑ b, (s • p + t • q) b * c b
          = s * (∑ b, p b * c b) + t * (∑ b, q b * c b) := by
        intro c
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => by ring
      rw [hexp, hexp]
      have h1 : s * (∑ b, p b * u₁ a' b) ≤ s * (∑ b, p b * u₁ a b) :=
        mul_le_mul_of_nonneg_left (hpbr a') hs
      have h2 : t * (∑ b, q b * u₁ a' b) ≤ t * (∑ b, q b * u₁ a b) :=
        mul_le_mul_of_nonneg_left (hqbr a') ht
      linarith
