-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.algHom_eq_or_eq_comp_frobTwo_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9cdcff94-6460-53fc-a66b-89479fb86cfd

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalOmega_frobTwo_frobTwo_and_exists_generator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing

set_option autoImplicit false

namespace O2Rigid

theorem eq_or_eq_of_mul_eq_zero {B : Type} [CommRing B] [IsLocalRing B] {a a' b : B}
    (h : (b - a) * (b - a') = 0) (hu : IsUnit (a - a')) : b = a ∨ b = a' := by
  by_cases h1 : IsUnit (b - a)
  · right
    have : b - a' = 0 := by
      obtain ⟨u, hu'⟩ := h1
      have := congrArg (fun x => (↑u⁻¹ : B) * x) h
      simp only [mul_zero] at this
      rwa [← mul_assoc, ← hu', Units.inv_mul, one_mul] at this
    exact sub_eq_zero.mp this
  · left
    by_cases h2 : IsUnit (b - a')
    · have : b - a = 0 := by
        obtain ⟨u, hu'⟩ := h2
        have := congrArg (fun x => x * (↑u⁻¹ : B)) h
        simp only [zero_mul] at this
        rwa [mul_assoc, ← hu', Units.mul_inv, mul_one] at this
      exact sub_eq_zero.mp this
    · exfalso
      have hm1 : b - a ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h1
      have hm2 : b - a' ∈ IsLocalRing.maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr h2
      have : a - a' ∈ IsLocalRing.maximalIdeal B := by
        have := Ideal.sub_mem _ hm2 hm1
        rwa [sub_sub_sub_cancel_left] at this
      exact (IsLocalRing.mem_maximalIdeal _).mp this hu

end O2Rigid

theorem solution

    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})

    (n : ℕ)
    (Fr₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hFr₂ : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) → Fr₂ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (B : Type) [CommRing B] [IsLocalRing B] [Algebra 𝒪 B]
    (ε ε' : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) :
    ε' = ε ∨ ε' = ε.comp Fr₂.toAlgHom := by
  obtain ⟨hsq, α, hunit, hadj, s, t, hα⟩ :=
    CerednikDrinfeld.FormalOmega.frobTwo_frobTwo_and_exists_generator 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max
      hOnr_alg hOnr_closed hFr n Fr₂ hFr₂

  have hα' : (Fr₂ α) ^ 2 = algebraMap 𝒪 _ s * Fr₂ α + algebraMap 𝒪 _ t := by
    have := congrArg Fr₂ hα
    rwa [map_pow, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at this
  have htr : α + Fr₂ α = algebraMap 𝒪 _ s := by
    have h1 : (Fr₂ α - α) * (α + Fr₂ α - algebraMap 𝒪 _ s) = 0 := by
      have := sub_eq_zero.mpr hα'
      linear_combination hα' - hα
    obtain ⟨u, hu⟩ := hunit
    have := congrArg (fun x => ((↑u⁻¹ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))) * x) h1
    simp only [mul_zero] at this
    rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
    exact sub_eq_zero.mp this
  have hnorm : α * Fr₂ α = - algebraMap 𝒪 _ t := by
    have : Fr₂ α = algebraMap 𝒪 _ s - α := by rw [← htr]; ring
    rw [this]; linear_combination (-1 : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) * hα

  set a := ε α with ha
  set a' := ε (Fr₂ α) with ha'
  set b := ε' α with hb
  have hprod : (b - a) * (b - a') = 0 := by
    have h1 : b ^ 2 = algebraMap 𝒪 B s * b + algebraMap 𝒪 B t := by
      have := congrArg ε' hα
      rwa [map_pow, map_add, map_mul, AlgHom.commutes, AlgHom.commutes] at this
    have h2 : a + a' = algebraMap 𝒪 B s := by rw [ha, ha', ← map_add, htr, AlgHom.commutes]
    have h3 : a * a' = - algebraMap 𝒪 B t := by rw [ha, ha', ← map_mul, hnorm, map_neg, AlgHom.commutes]
    linear_combination h1 - b * h2 + h3
  have hu : IsUnit (a - a') := by
    rw [ha, ha', ← map_sub]
    have : IsUnit (α - Fr₂ α) := by rw [← neg_sub]; exact hunit.neg
    exact this.map ε

  have hext : ∀ (φ ψ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B), φ α = ψ α → φ = ψ := by
    intro φ ψ hφψ
    have hle : Algebra.adjoin 𝒪 {α} ≤ AlgHom.equalizer φ ψ := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact hφψ
    rw [hadj, top_le_iff] at hle
    ext z
    have hz : z ∈ AlgHom.equalizer φ ψ := hle ▸ Algebra.mem_top
    exact hz
  rcases O2Rigid.eq_or_eq_of_mul_eq_zero hprod hu with h | h
  · left; exact hext ε' ε (by rw [← hb, ← ha, h])
  · right; exact hext ε' (ε.comp Fr₂.toAlgHom) (by rw [← hb, h, ha', AlgHom.comp_apply]; rfl)

end S_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_algHom_eq_or_eq_comp_frobTwo_of_isLocalRing (solution)
