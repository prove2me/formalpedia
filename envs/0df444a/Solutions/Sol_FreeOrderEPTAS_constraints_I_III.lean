-- Prove2me | solution 1 for FreeOrderEPTAS.constraints_I_III
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:49:37.008513+00:00
-- url     : https://prove2.me/submissions/2bfb2d8b-6be1-4976-ba2e-a1dca7d23976

import Mathlib
import Definitions.Def_FreeOrderEPTAS_mkLP
import Definitions.Def_FreeOrderEPTAS_IsInducedGuess
import Definitions.Def_FreeOrderEPTAS_IsDependentRounding

namespace Aux_FreeOrderEPTAS_constraints_I_III
open FreeOrderEPTAS

lemma sum_bit {n : ℕ} (s : Finset (Fin n)) (f : Fin n → Bool) :
    ∑ j ∈ s, bit (f j) = ((s.filter fun j => f j = true).card : ℝ) := by
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Bool.eq_false_or_eq_true (f j) with h | h <;> simp [bit, h]

end Aux_FreeOrderEPTAS_constraints_I_III

open Aux_FreeOrderEPTAS_constraints_I_III in
open FreeOrderEPTAS in
theorem solution {m D n : ℕ} (I : SCInstance m D n) (ϵ δ ξ : ℝ)
    (x : Assignment m n) (hcard : MeetsCard I x)
    (Nlo Nhi : Fin m → Fin (numTypes I ϵ δ) → ℕ)
    (Slo : Fin m → Fin D → Fin (numTypes I ϵ δ) → ℝ)
    (hg : IsInducedGuess I ϵ δ ξ x Nlo Nhi Slo)
    (y : (mkLP I ϵ δ ξ Nlo Nhi Slo).Vars) (hy : (mkLP I ϵ δ ξ Nlo Nhi Slo).MeetsS123 y)
    (rnd : Rounding) (hrnd : IsDependentRounding rnd)
    (Y : Assignment m n) (hY : Y ∈ (rnd (mkLP I ϵ δ ξ Nlo Nhi Slo) y).support) :
    MeetsCard I Y := by
  have hdeg := (hrnd _ _ hy).degree Y hY
  refine ⟨?_, ?_⟩
  · intro j
    have h2 : ∑ i, bit (Y i j) ≤ 1 := hdeg.1 j
    have h3 : ((Finset.univ.filter fun i => Y i j = true).card : ℝ) ≤ 1 := by
      rw [← sum_bit Finset.univ (fun i => Y i j)]
      exact h2
    exact_mod_cast h3
  · intro i
    have hS3 : ∀ t : Fin (numTypes I ϵ δ),
        ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), bit (Y i j) ≤ (Nhi i t : ℝ) :=
      fun t => (hdeg.2 i t).2
    have hNhi : ∀ t : Fin (numTypes I ϵ δ), (Nhi i t : ℝ) ≤ (Nip I ϵ δ x i t : ℝ) := by
      intro t
      by_cases h : (Nip I ϵ δ x i t : ℝ) ≤ 2 / δ
      · rw [(hg.exact i t h).2]
      · exact (hg.approx i t (lt_of_not_ge h)).2.2
    have hNip : ∀ t : Fin (numTypes I ϵ δ),
        ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), bit (x i j) =
          (Nip I ϵ δ x i t : ℝ) := by
      intro t
      rw [sum_bit, Finset.filter_filter]
      first | done | rfl
    have hY' : ((Finset.univ.filter fun j => Y i j = true).card : ℝ) ≤ (I.k i : ℝ) := by
      rw [← sum_bit Finset.univ (fun j => Y i j),
        ← Finset.sum_fiberwise Finset.univ (rho I ϵ δ) (fun j => bit (Y i j))]
      calc _ ≤ ∑ t, (Nhi i t : ℝ) := Finset.sum_le_sum fun t _ => hS3 t
        _ ≤ ∑ t, (Nip I ϵ δ x i t : ℝ) := Finset.sum_le_sum fun t _ => hNhi t
        _ = ∑ t, ∑ j ∈ Finset.univ.filter (fun j => rho I ϵ δ j = t), bit (x i j) :=
            Finset.sum_congr rfl fun t _ => (hNip t).symm
        _ = ∑ j, bit (x i j) := Finset.sum_fiberwise Finset.univ (rho I ϵ δ) (fun j => bit (x i j))
        _ = ((Finset.univ.filter fun j => x i j = true).card : ℝ) :=
            sum_bit Finset.univ (fun j => x i j)
        _ ≤ (I.k i : ℝ) := by exact_mod_cast hcard.2 i
    exact_mod_cast hY'
