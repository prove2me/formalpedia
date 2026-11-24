-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_frob_sgn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:40.125056+00:00
-- url     : https://prove2.me/submissions/bae95f4b-aebe-47f4-8f70-f02b0a429bb5

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card_under
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_lift
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_smul_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(L/ℚ))
    (H : IsArithFrobAt ℤ σ P) (x : L) (c : ℤ) (hx : x ^ 2 = (c : L)) (hpc : ¬ (p : ℤ) ∣ c) :
    ((sgn σ x : ℤˣ) : ℤ) = jacobiSym c p := by
  have hp : p.Prime := Fact.out
  have hmem := odd_intCast_mem_iff p P
  have hF : ∀ y : 𝓞 L, σ • y - y ^ p ∈ P := by
    intro y
    have := H y
    rw [odd_card_under p P] at this
    exact this
  obtain ⟨A, hAcoe, hA2⟩ := odd_lift x c hx
  have hσA := odd_smul_lift σ x c hx A hAcoe
  have hAnot : A ∉ P := by
    intro hA
    apply hpc
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hpow : A ^ p = A * (c : 𝓞 L) ^ (p / 2) := by
    rw [← hA2, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have hE : (p : ℤ) ∣ c ^ (p / 2) - legendreSym p c := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
    push_cast
    rfl
  have hE' : (c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L) ∈ P := by
    have := (hmem _).mpr hE
    push_cast at this
    exact this
  have hprod : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A ∈ P := by
    have heq : ((((sgn σ x : ℤˣ) : ℤ) - legendreSym p c : ℤ) : 𝓞 L) * A =
        (σ • A - A ^ p) + A * ((c : 𝓞 L) ^ (p / 2) - ((legendreSym p c : ℤ) : 𝓞 L)) := by
      rw [hσA, hpow]
      push_cast
      ring
    rw [heq]
    exact P.add_mem (hF A) (P.mul_mem_left A hE')
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hbad : ∀ n : ℤ, (n = 2 ∨ n = -2) → ¬ (p : ℤ) ∣ n := by
    rintro n (rfl | rfl) h
    · have := Int.le_of_dvd (by norm_num) h
      have := hp.two_le
      omega
    · have := Int.le_of_dvd (by norm_num) (dvd_neg.mpr h)
      have := hp.two_le
      omega
  rcases (inferInstance : P.IsPrime).mem_or_mem hprod with h | h
  · rw [hmem] at h
    have hL := legendreSym.eq_one_or_neg_one p (a := c)
      (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpc)
    rcases Int.units_eq_one_or (sgn σ x) with h1 | h1 <;>
      simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
      rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
      first | rfl | exact absurd h (hbad _ (by norm_num))
  · exact absurd h hAnot
end Formalism.TwoAdicCyclotomicDecomposition
