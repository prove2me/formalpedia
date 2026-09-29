-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/83c88545-78dc-5010-9f93-d14b60115401

import Mathlib
import Theorems.Thm_WittVector_exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal

set_option autoImplicit false

theorem solution
    (r : ℕ) [Fact r.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr]
    (ϖ : Onr) (hϖ : Ideal.span {ϖ} = Ideal.span {((r : ℕ) : Onr)})
    (hcomplete : IsAdicComplete (Ideal.span {ϖ}) Onr)
    (hmax : (Ideal.span {ϖ}).IsMaximal)
    (hclosed : ∀ q : Polynomial Onr, q.Monic → 0 < q.natDegree → ∃ x : Onr, Polynomial.eval x q ∈ Ideal.span {ϖ})
    (Fr : Onr ≃+* Onr) (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {ϖ}) :
    ∃ (k : Type) (_ : Field k) (_ : CharP k r) (_ : IsAlgClosed k) (e : WittVector r k ≃+* Onr)
      (q : Onr →+* k),
      (∀ x : WittVector r k, e (WittVector.frobenius x) = Fr (e x)) ∧
      Function.Surjective q ∧ RingHom.ker q = Ideal.span {ϖ} ∧
      (∀ x : WittVector r k, q (e x) = x.coeff 0) := by
  classical
  have hrprime : r.Prime := Fact.out
  haveI : (Ideal.span {ϖ}).IsMaximal := hmax
  letI : Field (Onr ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})

  let q : Onr →+* Onr ⧸ Ideal.span {ϖ} := Ideal.Quotient.mk (Ideal.span {ϖ})
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hqker : RingHom.ker q = Ideal.span {ϖ} := Ideal.mk_ker
  have hrmem : ((r : ℕ) : Onr) ∈ Ideal.span {ϖ} := by rw [hϖ]; exact Ideal.mem_span_singleton_self _

  haveI hchar : CharP (Onr ⧸ Ideal.span {ϖ}) r :=
    (CharP.charP_iff_prime_eq_zero hrprime).2 (by
      have : q ((r : ℕ) : Onr) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hrmem
      simpa using this)
  haveI : ExpChar (Onr ⧸ Ideal.span {ϖ}) r := ExpChar.prime hrprime

  haveI halg : IsAlgClosed (Onr ⧸ Ideal.span {ϖ}) := by
    refine IsAlgClosed.of_exists_root _ fun p hpm hpi => ?_
    have hlifts : p ∈ Polynomial.lifts q := by
      rw [Polynomial.lifts_iff_coeff_lifts]; intro n; exact hq _
    obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hpm
    have hpos : 0 < P.natDegree := by
      rw [hPdeg]; exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hpi)
    obtain ⟨x, hx⟩ := hclosed P hPmonic hpos
    refine ⟨q x, ?_⟩
    rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, Ideal.Quotient.eq_zero_iff_mem]
    exact hx

  have hp : ((r : ℕ) : Onr) ∈ nonZeroDivisors Onr :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hrprime.ne_zero)
  haveI : IsAdicComplete (Ideal.span {((r : ℕ) : Onr)}) Onr := by rw [← hϖ]; exact hcomplete

  have huniq : ∀ (q₀ : Onr →+* Onr ⧸ Ideal.span {ϖ}), Function.Surjective q₀ → RingHom.ker q₀ = Ideal.span {((r : ℕ) : Onr)} →
      ∀ g₁ g₂ : WittVector r (Onr ⧸ Ideal.span {ϖ}) →+* Onr,
        q₀.comp g₁ = WittVector.constantCoeff → q₀.comp g₂ = WittVector.constantCoeff → g₁ = g₂ := by
    intro q₀ hq₀ hker₀ g₁ g₂ h₁ h₂
    letI : Algebra Onr (Onr ⧸ Ideal.span {ϖ}) := q₀.toAlgebra
    obtain ⟨e', -, he'⟩ :=
      WittVector.exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete (𝓞 := Onr) r hp (k := Onr ⧸ Ideal.span {ϖ}) hq₀ hker₀
    exact (he' g₁ h₁).trans (he' g₂ h₂).symm

  have hqker' : RingHom.ker q = Ideal.span {((r : ℕ) : Onr)} := by rw [hqker, hϖ]
  obtain ⟨e, he, -⟩ :=
    WittVector.exists_ringEquiv_comp_eq_constantCoeff_of_isAdicComplete (𝓞 := Onr) r hp (k := Onr ⧸ Ideal.span {ϖ}) hq hqker'
  have he_apply : ∀ x : WittVector r (Onr ⧸ Ideal.span {ϖ}), q (e x) = x.coeff 0 := fun x => by
    have := RingHom.congr_fun he x
    simpa [Ideal.Quotient.algebraMap_eq] using this

  let φ : (Onr ⧸ Ideal.span {ϖ}) ≃+* (Onr ⧸ Ideal.span {ϖ}) := frobeniusEquiv (Onr ⧸ Ideal.span {ϖ}) r
  let q' : Onr →+* Onr ⧸ Ideal.span {ϖ} := (φ.symm : (Onr ⧸ Ideal.span {ϖ}) →+* (Onr ⧸ Ideal.span {ϖ})).comp q
  have hq' : Function.Surjective q' := φ.symm.surjective.comp hq
  have hq'ker : RingHom.ker q' = Ideal.span {((r : ℕ) : Onr)} := by
    rw [← hqker']; ext x
    simp only [RingHom.mem_ker, q', RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply,
      map_eq_zero_iff _ φ.symm.injective]

  have hqFr : ∀ y : Onr, q (Fr y) = q y ^ r := fun y => by
    have h := hFr y
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h₁ : q'.comp ((e : WittVector r (Onr ⧸ Ideal.span {ϖ}) →+* Onr).comp WittVector.frobenius) = WittVector.constantCoeff := by
    ext x
    simp only [q', RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply, WittVector.constantCoeff_apply]
    rw [he_apply, WittVector.coeff_frobenius_charP, ← frobenius_def, ← coe_frobeniusEquiv, RingEquiv.symm_apply_apply]
  have h₂ : q'.comp ((Fr : Onr →+* Onr).comp (e : WittVector r (Onr ⧸ Ideal.span {ϖ}) →+* Onr)) = WittVector.constantCoeff := by
    ext x
    simp only [q', RingHom.coe_comp, RingEquiv.coe_toRingHom, Function.comp_apply, WittVector.constantCoeff_apply]
    rw [hqFr, he_apply, ← frobenius_def, ← coe_frobeniusEquiv, RingEquiv.symm_apply_apply]
  have hcomm := huniq q' hq' hq'ker _ _ h₁ h₂
  refine ⟨Onr ⧸ Ideal.span {ϖ}, inferInstance, hchar, halg, e, q, fun x => ?_, hq, hqker, he_apply⟩
  exact RingHom.congr_fun hcomm x

end S_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringEquiv_wittVector_apply_frobenius_eq_of_isAdicComplete_of_isMaximal (solution)
