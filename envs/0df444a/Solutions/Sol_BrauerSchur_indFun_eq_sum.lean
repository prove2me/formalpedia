-- Prove2me | solution 1 for BrauerSchur.indFun_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:43.603225+00:00
-- url     : https://prove2.me/submissions/83a7e9d1-2cec-453d-902a-56b765ea0c11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced
import Theorems.Thm_BrauerSchur_dot_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open BrauerSchur
open scoped BigOperators
variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)
variable {m : ℕ} (t : Fin m → G)
namespace BrauerSchur
theorem _root_.solution [Fintype G] [CharZero K] (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j)
    (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) (g : G) :
    indFun H (fun h => ((ψ h : Kˣ) : K)) g = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by
  classical
  show (Nat.card H : K)⁻¹ * ∑ x : G, dot H ψ (x⁻¹ * g * x) = _
  let f : Fin m × H → G := fun p => t p.1 * p.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, h⟩ ⟨j, h'⟩ hij
      simp only [f] at hij
      have hij' : i = j := by
        rw [← ht i j]
        have e : (t i)⁻¹ * t j = (h : G) * (h' : G)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hij, inv_mul_cancel_left]
        rw [e]
        exact H.mul_mem h.2 (H.inv_mem h'.2)
      subst hij'
      have : (h : G) = h' := mul_left_cancel hij
      rw [Subtype.ext this]
    · intro x
      obtain ⟨i, hi⟩ := hc x
      exact ⟨⟨i, ⟨_, hi⟩⟩, by simp [f]⟩
  rw [← Fintype.sum_bijective f hf (fun p => dot H ψ ((f p)⁻¹ * g * f p)) _ (fun _ => rfl),
    Fintype.sum_prod_type]
  have hin : ∀ i, ∑ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) =
      (Fintype.card H : K) * dot H ψ ((t i)⁻¹ * g * t i) := by
    intro i
    have : ∀ h : H, dot H ψ ((f (i, h))⁻¹ * g * f (i, h)) = dot H ψ ((t i)⁻¹ * g * t i) := by
      intro h
      have e : (f (i, h))⁻¹ * g * f (i, h) = (h : G)⁻¹ * ((t i)⁻¹ * g * t i) * h := by
        simp only [f]
        group
      rw [e, dot_conj H ψ h.2]
    rw [Finset.sum_congr rfl fun h _ => this h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun i _ => hin i, ← Finset.mul_sum, ← mul_assoc, Nat.card_eq_fintype_card,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
end BrauerSchur
