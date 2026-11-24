-- Prove2me | solution 1 for Formalism.L2.DIV.conv_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:28.229713+00:00
-- url     : https://prove2.me/submissions/27ae18cc-72d2-4366-99da-381ccd237e3d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_IsAbsIrrChar_conj
import Theorems.Thm_Formalism_L2_DIV_convA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
open Representation
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace Formalism.L2.DIV
theorem _root_.solution {χ χ' : G → K} (h : IsAbsIrrChar χ) (h' : IsAbsIrrChar χ') (u : G) :
    (∑ s, χ s⁻¹ * χ' (s * u)) * χ' 1 = if χ = χ' then (Fintype.card G : K) * χ' u else 0 := by
  classical
  have hcl : ∀ g s, χ (g * s * g⁻¹)⁻¹ = χ s⁻¹ := by
    intro g s
    have := h.conj g s⁻¹
    simpa [mul_assoc] using this
  obtain ⟨n, ρ, hi, hρ⟩ := h
  obtain ⟨n', ρ', hi', hρ'⟩ := h'
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  have : Invertible ((Nat.card G : ℕ) : AlgebraicClosure K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : ((Nat.card G : ℕ) : AlgebraicClosure K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hA := convA ρ' (fun s => j (χ s⁻¹)) (fun g s => by simp only [hcl]) u
  have hfin : ((finrank (AlgebraicClosure K) (Fin n' → AlgebraicClosure K) : ℕ) : AlgebraicClosure K) =
      j (χ' 1) := by rw [← hρ', char_one]
  have hsum : (∑ s, j (χ s⁻¹) * ρ'.character s) =
      if χ = χ' then ((Nat.card G : ℕ) : AlgebraicClosure K) else 0 := by
    have ho := char_orthonormal ρ' ρ
    have e : (∑ s, j (χ s⁻¹) * ρ'.character s) = ∑ g, ρ'.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun s _ => by rw [hρ, mul_comm]
    rw [e]
    have hiff : Nonempty (Representation.Equiv ρ ρ') ↔ χ = χ' := by
      constructor
      · rintro ⟨φ⟩
        funext t
        apply hj
        rw [← hρ, ← hρ', char_iso φ]
      · intro hc
        by_contra hne
        rw [if_neg hne] at ho
        have ho' := card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ
        rw [IsIrreducible.finrank_intertwiningMap_self] at ho'
        have : ∀ g, ρ'.character g = ρ.character g := fun g => by rw [hρ, hρ', hc]
        simp only [this] at ho
        rw [ho] at ho'
        simp at ho'
    by_cases hc : χ = χ'
    · rw [if_pos hc]
      rw [if_pos (hiff.mpr hc)] at ho
      field_simp at ho
      simpa using ho
    · rw [if_neg hc]
      rw [if_neg (fun hh => hc (hiff.mp hh))] at ho
      simpa using ho
  apply hj
  rw [hfin, hsum] at hA
  simp only [hρ'] at hA
  rw [map_mul, map_sum]
  simp only [map_mul]
  rw [hA]
  split_ifs
  · rw [map_mul, map_natCast, Nat.card_eq_fintype_card]
  · simp
end Formalism.L2.DIV
