-- Prove2me | solution 1 for FCP.Jacobian.birational_keller_criterion
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:05:16.38387+00:00
-- url     : https://prove2.me/submissions/d7a56d0f-b1ea-4a45-b59e-efa1a8c01091

import Mathlib
import Definitions.Def_FCP_Jacobian
import Theorems.Thm_FCP_Jacobian_etale_and_flat_aeval_of_isUnit_jacobian


open scoped BigOperators

namespace FCP.Jacobian.Birational

/-- Flatness forces a reduced denominator to become a unit. -/
theorem denominator_isUnit_of_flat
    {R S : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    {a b : R} (hab : IsRelPrime b a) (s : S)
    (hs : algebraMap R S b * s = algebraMap R S a) :
    IsUnit (algebraMap R S b) := by
  classical
  have hrel : ∑ i : Fin 2, (![b, -a] : Fin 2 → R) i • (![s, 1] : Fin 2 → S) i = 0 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Algebra.smul_def, map_neg, mul_one]
    linear_combination hs
  obtain ⟨m, c, y, hc, hcy⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := S)
    (f := ![b, -a]) (x := ![s, 1]) hrel
  have hcdiv : ∀ j, b ∣ c 1 j := by
    intro j
    have h := hcy j
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      neg_mul] at h
    apply hab.dvd_of_dvd_mul_left
    refine ⟨c 0 j, ?_⟩
    linear_combination -h
  choose z hz using hcdiv
  apply isUnit_iff_exists_inv.mpr
  refine ⟨∑ j, algebraMap R S (z j) * y j, ?_⟩
  have h := hc 1
  simp only [Matrix.cons_val_one, Algebra.smul_def] at h
  rw [Finset.mul_sum]
  simpa only [hz, map_mul, mul_assoc, Matrix.cons_val_zero] using h.symm

/-- A flat birational extension of a factorial domain is trivial if it reflects units.
The birational hypothesis is written as explicit fraction representations. -/
theorem surjective_of_flat_birational
    {R S : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Flat R S]
    (hinj : Function.Injective (algebraMap R S))
    (hunit : ∀ r : R, IsUnit (algebraMap R S r) → IsUnit r)
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ algebraMap R S b * s = algebraMap R S a) :
    Function.Surjective (algebraMap R S) := by
  intro s
  obtain ⟨a, b, hb, hs⟩ := hfrac s
  obtain ⟨a', b', c, hab, ha, hb'⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b hb
  have hc : c ≠ 0 := by
    intro h
    simp [h] at hb'
    exact hb hb'.symm
  have hmc : algebraMap R S c ≠ 0 := by
    exact fun h => hc (hinj (by simpa using h))
  have hs' : algebraMap R S b' * s = algebraMap R S a' := by
    apply mul_left_cancel₀ hmc
    simpa only [← mul_assoc, ← map_mul, ha, hb'] using hs
  have hbunit := hunit b' (denominator_isUnit_of_flat hab.symm s hs')
  obtain ⟨u, hu⟩ := hbunit
  refine ⟨↑(u⁻¹) * a', ?_⟩
  rw [map_mul]
  have hmul : algebraMap R S ↑(u⁻¹) * algebraMap R S b' = 1 := by
    rw [← hu, ← map_mul]
    simp
  calc
    algebraMap R S ↑(u⁻¹) * algebraMap R S a' =
        algebraMap R S ↑(u⁻¹) * (algebraMap R S b' * s) := by rw [hs']
    _ = s := by rw [← mul_assoc, hmul, one_mul]

theorem injective_of_flat {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Nontrivial S] (f : R →+* S) (hf : f.Flat) :
    Function.Injective f := by
  algebraize [f]
  exact FaithfulSMul.algebraMap_injective R S

theorem surjective_ringHom_of_flat_birational
    {R S : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] (f : R →+* S) (hf : f.Flat)
    (hunit : ∀ r : R, IsUnit (f r) → IsUnit r)
    (hfrac : ∀ s : S, ∃ a b : R, b ≠ 0 ∧ f b * s = f a) :
    Function.Surjective f := by
  algebraize [f]
  exact surjective_of_flat_birational (FaithfulSMul.algebraMap_injective R S) hunit hfrac

end FCP.Jacobian.Birational


namespace FCP.Jacobian.Birational

open MvPolynomial

theorem aeval_reflects_units {k : Type} [Field k] {n : ℕ}
    (F : PolyMap k n) (hinj : Function.Injective (aeval (R := k) F))
    (p : MvPolynomial (Fin n) k) (hp : IsUnit (aeval (R := k) F p)) : IsUnit p := by
  obtain ⟨c, hc, hpc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hp
  have h : p = C c := hinj (by simpa using hpc)
  exact h ▸ hc.map C

/-- The birational hypothesis is an explicit equality-of-fraction-fields condition:
every target polynomial is a ratio of two substituted polynomials. -/
theorem exists_inverse_of_flat_birational {k : Type} [Field k] {n : ℕ}
    (F : PolyMap k n)
    (hflat : (aeval (R := k) F).toRingHom.Flat)
    (hfrac : ∀ p : MvPolynomial (Fin n) k,
      ∃ a b : MvPolynomial (Fin n) k, b ≠ 0 ∧ aeval (R := k) F b * p = aeval (R := k) F a) :
    ∃ G : PolyMap k n, comp G F = idMap k n ∧ comp F G = idMap k n := by
  classical
  have hinj := injective_of_flat (aeval (R := k) F).toRingHom hflat
  have hsurj : Function.Surjective (aeval (R := k) F) :=
    surjective_ringHom_of_flat_birational (aeval (R := k) F).toRingHom hflat
      (aeval_reflects_units F hinj) hfrac
  choose G hG using fun i : Fin n => hsurj (X i)
  have hGF : comp G F = idMap k n := funext hG
  refine ⟨G, hGF, ?_⟩
  funext i
  apply hinj
  change aeval (R := k) F (aeval (R := k) G (F i)) = aeval (R := k) F (X i)
  have hcomp : (aeval (R := k) F).comp (aeval (R := k) G) = AlgHom.id k (MvPolynomial (Fin n) k) := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using hG j
  change ((aeval (R := k) F).comp (aeval (R := k) G)) (F i) = _
  rw [hcomp]
  simp

end FCP.Jacobian.Birational

theorem solution {k : Type} [Field k] {n : ℕ}
    (F : FCP.Jacobian.PolyMap k n) (hF : IsUnit (FCP.Jacobian.jacobian F).det)
    (hfrac : ∀ p : MvPolynomial (Fin n) k,
      ∃ a b : MvPolynomial (Fin n) k,
        b ≠ 0 ∧ MvPolynomial.aeval (R := k) F b * p = MvPolynomial.aeval (R := k) F a) :
    ∃ G : FCP.Jacobian.PolyMap k n,
      FCP.Jacobian.comp G F = FCP.Jacobian.idMap k n ∧
      FCP.Jacobian.comp F G = FCP.Jacobian.idMap k n := by
  exact FCP.Jacobian.Birational.exists_inverse_of_flat_birational F
    (FCP.Jacobian.etale_and_flat_aeval_of_isUnit_jacobian F hF).2 hfrac
