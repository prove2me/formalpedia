-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layer_finrank_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:14.935828+00:00
-- url     : https://prove2.me/submissions/5835e41b-2eb8-40db-a68f-b569da9fb1b3

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_not_sq_cyc
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_pm_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ne_zero_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_klein_four_cover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal Polynomial
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {n q d : ℕ} {ζ a b : L}
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (h : IsLayer n q d ζ a b) (hn : 1 ≤ n) (hqd : HypOdd q d)
    [IsGalois ℚ L] : 2 ^ (n + 1) ≤ Module.finrank ℚ L := by
  obtain ⟨hζ, ha, hb, htop⟩ := h
  obtain ⟨hq, hd, hqd', hq2, hd2⟩ := hqd
  let K := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have : IsCyclotomicExtension {2 ^ n} ℚ K := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hKdeg : Module.finrank ℚ K = 2 ^ (n - 1) := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral ζ),
      ← cyclotomic_eq_minpoly_rat hζ (by positivity), natDegree_cyclotomic,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp
  have hns : ∀ (p : ℕ) (m : ℤ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ m → ∀ y : L, y ∈ K →
      y ^ 2 = ((p * m : ℤ) : L) → False := by
    intro p m hp hp2 hm y hy hy2
    have := Fact.mk hp
    have hpN : ¬ p ∣ 2 ^ n := fun hdvd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
    exact not_sq_cyc K (2 ^ n) p hpN m hm ⟨y, hy⟩ (by ext; simpa using hy2)
  have hndvd1 : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ -1 := by
    intro p hp hdvd
    have := Int.eq_one_of_dvd_one (by positivity) ((dvd_neg).mp hdvd)
    have : p = 1 := by exact_mod_cast this
    exact hp.one_lt.ne' this
  have hqd_dvd : ¬ (q : ℤ) ∣ (d : ℤ) := by
    intro hdvd
    have : q ∣ d := by exact_mod_cast hdvd
    exact hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp this)
  have haK : a ∉ K := fun haK => hns q (-1) hq hq2 (hndvd1 q hq) a haK (by push_cast; rw [ha]; ring)
  have hbK : b ∉ K := fun hbK => hns d (-1) hd hd2 (hndvd1 d hd) b hbK (by push_cast; rw [hb]; ring)
  have habK : a * b ∉ K := fun habK => hns q d hq hq2 hqd_dvd (a * b) habK
    (by rw [mul_pow, ha, hb]; push_cast; ring)
  have hfix : IntermediateField.fixedField K.fixingSubgroup = K := IsGalois.fixedField_fixingSubgroup K
  have hmove : ∀ y : L, y ∉ K → ∃ σ ∈ K.fixingSubgroup, σ y ≠ y := by
    intro y hy
    by_contra hc
    push Not at hc
    apply hy
    rw [← hfix]
    exact (IntermediateField.mem_fixedField_iff _ _).mpr hc
  obtain ⟨σ1, hσ1, h1⟩ := hmove a haK
  obtain ⟨σ2, hσ2, h2⟩ := hmove b hbK
  obtain ⟨σ3, hσ3, h3⟩ := hmove (a * b) habK
  have ha0 := ne_zero_of_sq hq.ne_zero ha
  have hb0 := ne_zero_of_sq hd.ne_zero hb
  let s : Gal(L/ℚ) →* ℤˣ × ℤˣ := (sgnHom a ha0 (pm_of_sq ha)).prod (sgnHom b hb0 (pm_of_sq hb))
  have hs : ∀ σ, s σ = (sgn σ a, sgn σ b) := fun σ => rfl
  have hu : (s σ1).1 = -1 := by
    rw [hs]
    exact sgn_of_neg ha0 ((pm_of_sq ha σ1).resolve_left h1)
  have hv : (s σ2).2 = -1 := by
    rw [hs]
    exact sgn_of_neg hb0 ((pm_of_sq hb σ2).resolve_left h2)
  have hw : (s σ3).1 * (s σ3).2 = -1 := by
    rw [hs]
    rw [map_mul] at h3
    rcases pm_of_sq ha σ3 with e1 | e1 <;> rcases pm_of_sq hb σ3 with e2 | e2
    · exact absurd (by rw [e1, e2]) h3
    · rw [sgn_of_eq e1, sgn_of_neg hb0 e2]; rfl
    · rw [sgn_of_neg ha0 e1, sgn_of_eq e2]; rfl
    · exact absurd (by rw [e1, e2, neg_mul_neg]) h3
  let φ : K.fixingSubgroup → ℤˣ × ℤˣ := fun σ => s σ
  have hφ : Function.Surjective φ := by
    intro t
    rcases klein_four_cover (s σ1) (s σ2) (s σ3) t hu hv hw with e | e | e | e | e | e | e
    · exact ⟨1, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩, e.symm⟩
    · exact ⟨⟨σ2, hσ2⟩, e.symm⟩
    · exact ⟨⟨σ3, hσ3⟩, e.symm⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ2, hσ2⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ1, hσ1⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
    · exact ⟨⟨σ2, hσ2⟩ * ⟨σ3, hσ3⟩, by simp [φ, e]⟩
  have hH : 4 ≤ Nat.card K.fixingSubgroup := by
    have := Nat.card_le_card_of_surjective φ hφ
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
  have hLK : Module.finrank K L = Nat.card K.fixingSubgroup :=
    (IsGalois.card_fixingSubgroup_eq_finrank K).symm
  rw [← Module.finrank_mul_finrank ℚ K L, hKdeg, hLK]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  calc 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
    _ ≤ 2 ^ k * Nat.card K.fixingSubgroup := Nat.mul_le_mul_left _ hH
end Formalism.TwoAdicCyclotomicDecomposition
