-- Prove2me | solution 1 for Formalism.Q3.mqFrob_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:13.286661+00:00
-- url     : https://prove2.me/submissions/12d582c3-fb4d-452d-b712-735b595d4535

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQFrob
import Theorems.Thm_Formalism_Q3_mqFrob_intCast_mem_iff
import Theorems.Thm_Formalism_Q3_mqFrob_card

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
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hG : MQGalois) : MQFrob := by
  intro k E _ _ a α hMQ ha p _ P hPp _ σ H i
  have hp : p.Prime := Fact.out
  have hmem := mqFrob_intCast_mem_iff p P
  have hF : ∀ x : 𝓞 E, σ • x - x ^ p ∈ P := by
    intro x
    have := H x
    rw [mqFrob_card p P] at this
    exact this
  have hsq : α i ^ 2 = (a i : E) := hMQ.1 i
  have hσ : σ (α i) = (((galSign α σ i : ℤˣ) : ℤ) : E) * α i := (hG k E a α hMQ ha).2.1 σ i
  have hint : IsIntegral ℤ (α i) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [hsq, ← eq_intCast (algebraMap ℤ E)]
    exact isIntegral_algebraMap
  obtain ⟨A, hAcoe⟩ : ∃ A : 𝓞 E, (A : E) = α i := ⟨⟨α i, hint⟩, rfl⟩
  have hA2 : A ^ 2 = (a i : 𝓞 E) := by
    apply RingOfIntegers.coe_injective
    simp [hAcoe, hsq]
  have hσA : σ • A = (((galSign α σ i : ℤˣ) : ℤ) : 𝓞 E) * A := by
    apply RingOfIntegers.coe_injective
    show σ (A : E) = _
    rw [hAcoe, hσ]
    simp [hAcoe]
  have hAnot : ¬ (p : ℤ) ∣ a i → A ∉ P := by
    intro hpa hA
    apply hpa
    rw [← hmem, ← hA2]
    exact P.pow_mem_of_mem hA 2 (by norm_num)
  refine ⟨fun hnd => ?_, fun hp2 ha4 => ?_⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hnd (by push_cast; exact dvd_mul_right 2 _)
    have hpa : ¬ (p : ℤ) ∣ a i := fun h => hnd (dvd_mul_of_dvd_right h 2)
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hpow : A ^ p = A * (a i : 𝓞 E) ^ (p / 2) := by
      rw [← hA2, ← pow_mul, ← pow_succ']
      congr 1
      omega
    have hE : (p : ℤ) ∣ (a i) ^ (p / 2) - legendreSym p (a i) := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, legendreSym.eq_pow]
      push_cast
      rfl
    have hE' : (a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E) ∈ P := by
      have := (hmem _).mpr hE
      push_cast at this
      exact this
    have hprod : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A ∈ P := by
      have heq : ((((galSign α σ i : ℤˣ) : ℤ) - legendreSym p (a i) : ℤ) : 𝓞 E) * A =
          (σ • A - A ^ p) + A * ((a i : 𝓞 E) ^ (p / 2) - ((legendreSym p (a i) : ℤ) : 𝓞 E)) := by
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
      have hL := legendreSym.eq_one_or_neg_one p (a := a i)
        (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpa)
      rcases Int.units_eq_one_or (galSign α σ i) with h1 | h1 <;>
        simp only [h1, Units.val_one, Units.val_neg] at h ⊢ <;>
        rcases hL with h2 | h2 <;> rw [h2] at h ⊢ <;>
        first | rfl | exact absurd h (hbad _ (by norm_num))
    · exact absurd h (hAnot hpa)
  ·
    subst hp2
    obtain ⟨c, hc⟩ : ∃ c : ℤ, a i = 4 * c + 1 := ⟨(a i - 1) / 4, by omega⟩
    have hcE : (a i : E) = 4 * c + 1 := by exact_mod_cast hc
    obtain ⟨ω, hωdef⟩ : ∃ ω : E, ω = (1 + α i) / 2 := ⟨_, rfl⟩
    have hω2 : ω ^ 2 = ω + (c : E) := by
      rw [hωdef]
      linear_combination (1 / 4 : E) * hsq + (1 / 4 : E) * hcE
    have hωint : IsIntegral ℤ ω := by
      refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
      · apply Polynomial.monic_X_pow_sub
        rw [Polynomial.degree_X_add_C]
        norm_num
      · rw [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C,
          Polynomial.eval₂_X_pow, hω2]
        simp
    obtain ⟨W, hWcoe⟩ : ∃ W : 𝓞 E, (W : E) = ω := ⟨⟨ω, hωint⟩, rfl⟩
    have hW2 : W ^ 2 = W + (c : 𝓞 E) := by
      apply RingOfIntegers.coe_injective
      simp [hWcoe, hω2]
    have h2P : (2 : 𝓞 E) ∈ P := by
      have := (hmem 2).mpr (by norm_num)
      exact_mod_cast this
    have hs : galSign α σ i = 1 ∨ galSign α σ i = -1 := by
      unfold galSign
      split_ifs <;> simp
    have hFW := hF W
    rcases hs with hs | hs
    · have hσW : σ • W = W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = (W : E)
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        simp
      rw [hσW, hW2, show W - (W + (c : 𝓞 E)) = ((-c : ℤ) : 𝓞 E) by push_cast; ring, hmem] at hFW
      push_cast at hFW
      simp only [hs, true_iff]
      omega
    · have hσW : σ • W = 1 - W := by
        apply RingOfIntegers.coe_injective
        show σ (W : E) = ((1 - W : 𝓞 E) : E)
        have hc1 : ((1 - W : 𝓞 E) : E) = 1 - (W : E) := by simp
        rw [hc1]
        rw [hWcoe, hωdef, map_div₀, map_add, map_one, hσ, hs, map_ofNat]
        push_cast
        ring
      rw [hσW, hW2, show 1 - W - (W + (c : 𝓞 E)) = ((1 - c : ℤ) : 𝓞 E) - 2 * W by push_cast; ring]
        at hFW
      have h1c : ((1 - c : ℤ) : 𝓞 E) ∈ P := by
        have := P.add_mem hFW (P.mul_mem_right W h2P)
        simpa using this
      rw [hmem] at h1c
      push_cast at h1c
      rw [hs]
      constructor
      · intro h
        have := congrArg (fun u : ℤˣ => (u : ℤ)) h
        simp at this
      · intro h
        omega
end Formalism.Q3
