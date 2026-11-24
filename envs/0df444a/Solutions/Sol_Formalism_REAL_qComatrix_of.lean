-- Prove2me | solution 1 for Formalism.REAL.qComatrix_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:45:07.150889+00:00
-- url     : https://prove2.me/submissions/70b9b0d6-53a2-423f-bac2-2db34b2c14a9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_quantumMinor_eq_zero_of_col_eq
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_sign_cycleToLast
import Theorems.Thm_Formalism_REAL_quantumMinor_expand_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hr : QSkewRow) (hc : QSkewCol) : QComatrix := by
  unfold QComatrix
  intro A _ _ m E hE u i l
  obtain ⟨b', hbc, hbl⟩ : ∃ b' : Fin (m + 1) → Fin (m + 1),
      (∀ k : Fin m, b' k.castSucc = i.succAbove k) ∧ b' (Fin.last m) = l :=
    ⟨Fin.snoc (α := fun _ => Fin (m + 1)) (fun k => i.succAbove k) l, fun k => by simp, by simp⟩
  have hexp := quantumMinor_expand_last E id b' u
  have hbc' : b' ∘ Fin.castSucc = Fin.succAbove i := funext hbc
  rw [hbc', hbl] at hexp
  simp only [Function.id_comp, id_eq] at hexp
  have hsign : ∀ j : Fin (m + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) =
      (-1) ^ (m - (i : ℕ)) * (-1) ^ (m - (j : ℕ)) := by
    intro j
    rw [← pow_add]
    have hi := i.isLt
    have hj := j.isLt
    rcases Nat.even_or_odd ((i : ℕ) + j) with h | h
    · rw [h.neg_one_pow, Even.neg_one_pow]
      rw [Nat.even_iff] at h ⊢
      omega
    · rw [h.neg_one_pow, Odd.neg_one_pow]
      rw [Nat.odd_iff] at h ⊢
      omega
  have hL : ∑ j : Fin (m + 1), (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) *
          qminor E (Fin.succAbove j) (Fin.succAbove i) u * Tm E (u - (m : ℂ)) j l =
      (((-1 : ℤ) ^ (m - (i : ℕ)) : ℤ) : A) * qminor E id b' u := by
    rw [hexp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hsign j, Int.cast_mul, mul_assoc]
  rw [hL]
  by_cases hil : i = l
  · rw [if_pos hil, qdet]
    have hb : b' = id ∘ (cycleToLast m i) := by
      funext x
      refine Fin.lastCases ?_ (fun k => ?_) x
      · rw [hbl]; simp [cycleToLast_last, hil]
      · rw [hbc]; simp [cycleToLast_castSucc]
    rw [hb, hc A (m + 1) (m + 1) E hE id id (cycleToLast m i) u, sign_cycleToLast,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_assoc, ← Int.cast_mul, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, Int.cast_one, one_mul]
  · rw [if_neg hil]
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq (Ne.symm hil)
    rw [quantumMinor_eq_zero_of_col_eq hc E hE id b' u z.castSucc (Fin.last m) (Fin.castSucc_lt_last z).ne
      (by rw [hbc, hbl, hz]), mul_zero]
end Formalism.REAL
