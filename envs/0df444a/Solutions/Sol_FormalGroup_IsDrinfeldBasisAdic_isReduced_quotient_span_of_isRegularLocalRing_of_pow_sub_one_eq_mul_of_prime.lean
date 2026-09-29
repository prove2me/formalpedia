-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/fdb3d4d8-a236-5629-8fb6-55d4965b53d4

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
import Theorems.Thm_FormalGroup_IsDrinfeldBasisAdic_exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_Associated_of_pow_eq_units_mul_pow
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul
import Theorems.Thm_MvPowerSeries_isReduced_residueField_tensorProduct_quotient_span_C_mul_sub_mul_of_sub_drinfeldForm_mem_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid MvFormalGroup.instIsCommAddMv MvFormalGroup.instIsCommOfFormalGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.mk.injEq MvFormalGroup.nthSeries_zero MvFormalGroup.Hom.mk.sizeOf_spec MvFormalGroup.Hom.mk.injEq MvFormalGroup.mk.sizeOf_spec MvFormalGroup.e3_one MvFormalGroup.e3_zero MvFormalGroup.e3_two MvFormalGroup.e2_one MvFormalGroup.e2_zero FormalGroup.LawHom.ofMvHom_series MvFormalGroup.e1_apply FormalGroup.LawHom.toMvHom_toPowerSeries"

set_option autoImplicit false

open IsLocalRing

section AuxOpen

open Polynomial

namespace DrinformAux

lemma prod_sub_prod_mem_pow {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] (s : Finset ι) (I : Ideal R)
    (P L : ι → R) (hL : ∀ i ∈ s, L i ∈ I) (hPL : ∀ i ∈ s, P i - L i ∈ I ^ 2) :
    (∏ i ∈ s, P i) - (∏ i ∈ s, L i) ∈ I ^ (s.card + 1) ∧ (∏ i ∈ s, L i) ∈ I ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hL i (Finset.mem_insert_of_mem hi))
      (fun i hi => hPL i (Finset.mem_insert_of_mem hi))
    have hLa : L a ∈ I := hL a (Finset.mem_insert_self a s)
    have hPLa : P a - L a ∈ I ^ 2 := hPL a (Finset.mem_insert_self a s)
    have hPa : P a ∈ I := by
      have h := I.add_mem (Ideal.pow_le_self two_ne_zero hPLa) hLa
      simpa using h
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨?_, ?_⟩
    · have hsplit : P a * ∏ i ∈ s, P i - L a * ∏ i ∈ s, L i =
          P a * (∏ i ∈ s, P i - ∏ i ∈ s, L i) + (P a - L a) * ∏ i ∈ s, L i := by ring
      rw [hsplit]
      refine Ideal.add_mem _ ?_ ?_
      · have h := Ideal.mul_mem_mul hPa ih1
        rwa [← pow_succ'] at h
      · have h := Ideal.mul_mem_mul hPLa ih2
        rwa [← pow_add, show 2 + s.card = s.card + 1 + 1 by omega] at h
    · have h := Ideal.mul_mem_mul hLa ih2
      rwa [← pow_succ'] at h

section Universal

variable (q : ℕ) [hq : Fact q.Prime]

lemma prod_X_add_C_mul :
    ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X)) =
      X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X := by
  classical
  have hq1 : 1 < q := hq.out.one_lt
  have hq0 : q ≠ 0 := hq.out.ne_zero

  set p : Polynomial (Polynomial (ZMod q)) := X ^ q - C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X with hp
  have hdeg1 : (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (by simp)
  have hmonic : p.Monic := by
    apply (monic_X_pow q).sub_of_left
    calc degree (C ((X : Polynomial (ZMod q)) ^ (q - 1)) * X) ≤ 1 := by
            exact (degree_le_natDegree).trans (by exact_mod_cast hdeg1)
      _ < degree ((X : Polynomial (Polynomial (ZMod q))) ^ q) := by
            rw [degree_X_pow]; exact_mod_cast hq1
  have hnat : p.natDegree = q := by
    rw [hp, natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
    exact lt_of_le_of_lt hdeg1 hq1

  have hroot : ∀ c : ZMod q, p.IsRoot (C c * X) := by
    intro c
    simp only [hp, IsRoot, eval_sub, eval_pow, eval_X, eval_mul, eval_C, mul_pow, ← C_pow, ZMod.pow_card]
    rw [sub_eq_zero, mul_comm (X ^ (q - 1)) (C c * X), mul_assoc, mul_pow_sub_one hq0]
  have hinj : Function.Injective (fun c : ZMod q => C c * (X : Polynomial (ZMod q))) := by
    intro c d h
    have := congrArg (fun f : Polynomial (ZMod q) => f.coeff 1) h
    simpa using this
  set m : Multiset (Polynomial (ZMod q)) := (Finset.univ : Finset (ZMod q)).val.map (fun c => C c * X) with hm
  have hm_nodup : m.Nodup := Multiset.Nodup.map hinj Finset.univ.nodup
  have hm_le : m ≤ p.roots := by
    rw [Multiset.le_iff_subset hm_nodup]
    intro a ha
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (mem_roots hmonic.ne_zero).mpr (hroot c)
  have hcard : m.card = q := by simp [hm, ZMod.card]
  have hroots : p.roots = m :=
    (Multiset.eq_of_le_of_card_le hm_le (by rw [hcard]; exact (card_roots' p).trans hnat.le)).symm
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic (by rw [hroots, hcard, hnat])
  rw [hroots, hm, Multiset.map_map] at hprod

  calc ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) + C (C c * X))
      = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C (-c) * X)) :=
          Finset.prod_congr rfl (fun c _ => by simp)
    _ = ∏ c : ZMod q, ((X : Polynomial (Polynomial (ZMod q))) - C (C c * X)) :=
          Fintype.prod_equiv (Equiv.neg (ZMod q)) _ _ (fun c => rfl)
    _ = (Multiset.map ((fun a => X - C a) ∘ fun c => C c * X) (Finset.univ : Finset (ZMod q)).val).prod := by
          rw [Finset.prod_eq_multiset_prod]; rfl
    _ = p := hprod

lemma prod_add_mul_eq {B : Type*} [CommRing B] (ψ : ZMod q →+* B) (a b : B) :
    ∏ c : ZMod q, (a + ψ c * b) = a ^ q - b ^ (q - 1) * a := by
  have h := congrArg (eval₂RingHom (eval₂RingHom ψ b) a) (prod_X_add_C_mul q)
  simp only [map_prod, map_add, map_sub, map_mul, map_pow] at h
  simpa [Polynomial.coe_eval₂RingHom, eval₂_X, eval₂_C] using h

end Universal

end DrinformAux

end AuxOpen

namespace SSFGallq

open Polynomial

section DrinP

variable (q : ℕ) [hq : Fact q.Prime]

noncomputable def drinP : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 * ∏ c : ZMod q, (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0) -
    (MvPolynomial.X 0 * MvPolynomial.X 1 ^ q - MvPolynomial.X 0 ^ q * MvPolynomial.X 1)

theorem drinP_isHomogeneous : (drinP q).IsHomogeneous (q + 1) := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X _ _
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X _ _
  have hlin : ∀ c : ZMod q,
      (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).IsHomogeneous 1 := by
    intro c
    refine hX1.add ?_
    have := (MvPolynomial.isHomogeneous_C (Fin 2) (((c.val : ℕ) : ℤ))).mul hX0
    rwa [zero_add] at this
  have hprod : (∏ c : ZMod q, (MvPolynomial.X 1 + MvPolynomial.C (((c.val : ℕ) : ℤ)) * MvPolynomial.X 0 :
      MvPolynomial (Fin 2) ℤ)).IsHomogeneous q := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (ZMod q)) _ (fun _ => 1) (fun c _ => hlin c)
    rwa [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at this
  unfold drinP
  refine MvPolynomial.IsHomogeneous.sub ?_ (MvPolynomial.IsHomogeneous.sub ?_ ?_)
  · have := hX0.mul hprod; rwa [add_comm] at this
  · have := hX0.mul (hX1.pow q); rwa [one_mul, add_comm] at this
  · have := (hX0.pow q).mul hX1; rwa [one_mul] at this

theorem map_drinP_eq_zero : MvPolynomial.map (Int.castRingHom (ZMod q)) (drinP q) = 0 := by
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have key := DrinformAux.prod_add_mul_eq q (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)))
    (MvPolynomial.X 1) (MvPolynomial.X 0)
  unfold drinP
  simp only [map_sub, map_mul, map_prod, map_add, map_pow, MvPolynomial.map_X, MvPolynomial.map_C, map_natCast]
  have hC : ∀ c : ZMod q, ((c.val : ℕ) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c
    rw [← map_natCast (algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q))), ZMod.natCast_zmod_val]
  have hC2 : ∀ c : ZMod q, (MvPolynomial.C ((c.val : ℕ) : ZMod q) : MvPolynomial (Fin 2) (ZMod q)) =
      algebraMap (ZMod q) (MvPolynomial (Fin 2) (ZMod q)) c := by
    intro c; rw [ZMod.natCast_zmod_val]; rfl
  simp only [hC, hC2]
  rw [key, ← pow_sub_one_mul hq0 (MvPolynomial.X 0 : MvPolynomial (Fin 2) (ZMod q))]
  ring

theorem dvd_coeff_drinP (m : Fin 2 →₀ ℕ) : (q : ℤ) ∣ MvPolynomial.coeff m (drinP q) := by
  have h := congrArg (MvPolynomial.coeff m) (map_drinP_eq_zero q)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h

theorem mul_prod_sub_drinfeldForm_mem_pow
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hqm : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
  classical

  obtain ⟨h1, -⟩ := DrinformAux.prod_sub_prod_mem_pow (Finset.univ : Finset (ZMod q)) 𝔪 P
    (fun c => x₁ + ((c.val : ℕ) : R) * x₀)
    (fun c _ => 𝔪.add_mem hx₁ (𝔪.mul_mem_left _ hx₀)) (fun c _ => hP c)
  rw [Finset.card_univ, ZMod.card] at h1

  have h3 : x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by
    have heval : MvPolynomial.eval₂Hom (Int.castRingHom R) (![x₀, x₁] : Fin 2 → R) (drinP q) =
        x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) := by
      unfold drinP
      simp only [map_sub, map_mul, map_prod, map_add, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C,
        map_natCast, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← heval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
    refine Ideal.sum_mem _ fun m hm => ?_
    obtain ⟨k, hk⟩ := dvd_coeff_drinP q m
    have hdeg : m 0 + m 1 = q + 1 := by
      have hw := drinP_isHomogeneous q (MvPolynomial.mem_support_iff.mp hm)
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hw
    rw [hk, map_mul, map_natCast, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    have hmon : x₀ ^ m 0 * x₁ ^ m 1 ∈ 𝔪 ^ (q + 1) := by
      rw [← hdeg, pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx₀ _) (Ideal.pow_mem_pow hx₁ _)
    have : ((q : ℕ) : R) * (Int.castRingHom R k) * (x₀ ^ m 0 * x₁ ^ m 1) ∈ 𝔪 ^ (q + 2) := by
      rw [pow_succ']; exact Ideal.mul_mem_mul (𝔪.mul_mem_right _ hqm) hmon
    simpa [mul_assoc] using this
  have hsplit : x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) =
      x₀ * ((∏ c : ZMod q, P c) - ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀)) +
        (x₀ * ∏ c : ZMod q, (x₁ + ((c.val : ℕ) : R) * x₀) - (x₀ * x₁ ^ q - x₀ ^ q * x₁)) := by ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ h3
  have h := Ideal.mul_mem_mul hx₀ h1
  rwa [← pow_succ', show q + 1 + 1 = q + 2 by ring] at h

end DrinP

theorem ramifiedCoef
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W) (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (g : W →+* R) (_ : IsLocalHom g),
      g.comp σ = ι ∧ ∀ r : R, ∃ w : W, r - g w ∈ maximalIdeal R := by
  letI : Algebra A R := ι.toAlgebra
  haveI : IsLocalHom (algebraMap A R) := ‹IsLocalHom ι›
  obtain ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hsurj, hcomp⟩ :=
    IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField A ϖ hϖ R
  refine ⟨W, iW1, iW2, iW3, iW4, σ, hσ, τ, hτ, hcomp, fun r => ?_⟩
  obtain ⟨w, hw⟩ := hsurj (residue R r)
  refine ⟨w, ?_⟩
  rw [RingHom.comp_apply] at hw
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hw.symm

theorem chart
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (σ : A →+* W)
      (_ : maximalIdeal W = Ideal.span {σ ϖ})
      (f u v : MvPowerSeries (Fin 2) W) (_ : IsUnit u) (_ : IsUnit v)
      (_ : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈
        (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W), MvPowerSeries.X 1}) ^ (q + 2))
      (e : R ≃+* MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}),
      (∀ a : A, e (ι a) = Ideal.Quotient.mk _ (MvPowerSeries.C (σ a))) ∧
      e x₀ = Ideal.Quotient.mk _ (MvPowerSeries.X 0) ∧ e x₁ = Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by

  have hx₀ : x₀ ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)
  have hx₁ : x₁ ∈ maximalIdeal R := hmax ▸ Ideal.subset_span (by simp)

  obtain ⟨W, _, _, _, _, σ, hσ, g, _, hgσ, hres⟩ :=
    ramifiedCoef R A ϖ hϖ ι

  obtain ⟨u, hu, P, hP, hq'⟩ := FormalGroup.IsDrinfeldBasisAdic.exists_natCast_eq_mul_prod_pow_sub_one_of_isAdicComplete q R F x₀ x₁ hx₀ hx₁ hD
  set Fd : R := x₀ * ∏ c : ZMod q, P c with hFd

  haveI : IsRegularLocalRing R := hreg
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R (le_of_eq hdim)

  have hιq : ι ((q : ℕ) : A) = ((q : ℕ) : R) := map_natCast ι q
  have hpow : (ι ϖ) ^ (q - 1) = (ι ε * u) * Fd ^ (q - 1) := by
    rw [← map_pow, hϖq, map_mul, hιq, hq', mul_assoc]
  have hunit : IsUnit (ι ε * u) := (hε.map ι).mul hu
  obtain ⟨w, hw⟩ : Associated (ι ϖ) Fd := by
    have hq1 : q - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      omega
    exact Associated.of_pow_eq_units_mul_pow (ι ϖ) Fd (q - 1) hq1 hunit.unit (by simpa using hpow)

  have hπF : g (σ ϖ) = ((w⁻¹ : Rˣ) : R) * Fd := by
    have : ι ϖ = g (σ ϖ) := by rw [← RingHom.comp_apply, hgσ]
    rw [← this, ← hw, mul_comm (ι ϖ) (w : R), ← mul_assoc, Units.inv_mul, one_mul]

  have hFd_mem : Fd ∈ maximalIdeal R ^ (q + 1) := by
    have h1 : (∏ c : ZMod q, P c) ∈ maximalIdeal R ^ q := by
      have hPc : ∀ c : ZMod q, P c ∈ maximalIdeal R := by
        intro c
        have h2 : P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ maximalIdeal R :=
          Ideal.pow_le_self (by norm_num) (hP c)
        have h3 : x₁ + ((c.val : ℕ) : R) * x₀ ∈ maximalIdeal R :=
          Ideal.add_mem _ hx₁ (Ideal.mul_mem_left _ _ hx₀)
        simpa using Ideal.add_mem _ h2 h3
      have := Ideal.prod_mem_prod (s := (Finset.univ : Finset (ZMod q))) (fun c _ => hPc c)
      simpa [Finset.prod_const, ZMod.card] using this
    have : x₀ * ∏ c : ZMod q, P c ∈ maximalIdeal R ^ (1 + q) := by
      rw [pow_add]; exact Ideal.mul_mem_mul (by simpa using hx₀) h1
    simpa [hFd, add_comm] using this
  have hqmem : ((q : ℕ) : R) ∈ maximalIdeal R := by
    have hq1 : q - 1 ≠ 0 := by
      have := (Fact.out : q.Prime).two_le
      omega
    rw [hq']
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.pow_le_self (by omega) hFd_mem) _ (Nat.pos_of_ne_zero hq1))

  have hF : Fd - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ maximalIdeal R ^ (q + 2) :=
    mul_prod_sub_drinfeldForm_mem_pow q R (maximalIdeal R) hqmem x₀ x₁ hx₀ hx₁ P hP

  obtain ⟨f, u', v, hu', hv, hf, e, hconst, he₀, he₁⟩ :=
    IsRegularLocalRing.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_eq_mul q R hreg hdim x₀ x₁ hmax W (σ ϖ) hσ g hres Fd ((w⁻¹ : Rˣ) : R) (Units.isUnit _) hπF hF
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, σ, hσ, f, u', v, hu', hv, hf, e, ?_, he₀, he₁⟩
  intro a
  have hιa : g (σ a) = ι a := by rw [← RingHom.comp_apply, hgσ]
  simpa only [hιa] using hconst (σ a)

end SSFGallq

theorem solution
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (hreg : IsRegularLocalRing R) (hdim : ringKrullDim R = 2)
    (hchar : CharP (ResidueField R) q) [Finite (ResidueField R)]
    (F : FormalGroup R) [F.IsComm]
    (x₀ x₁ : R) (hmax : maximalIdeal R = Ideal.span {x₀, x₁})
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q x₀ x₁)

    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (ε : A) (hε : IsUnit ε) (hϖq : ϖ ^ (q - 1) = ε * (q : A))
    (ι : A →+* R) [IsLocalHom ι] :
    IsReduced (R ⧸ Ideal.span {ι ϖ}) := by

  classical
  obtain ⟨W, _iW1, _iW2, _iW3, _iW4, σ, hWm, f, u, v, hu, hv, hf, e, he, -, -⟩ :=
    SSFGallq.chart
      q R hreg hdim hchar F x₀ x₁ hmax hD A ϖ hϖ ε hε hϖq ι
  letI : CommRing W := _iW1
  haveI : IsDomain W := _iW2
  haveI : IsDiscreteValuationRing W := _iW3

  have hσϖ : σ ϖ ∈ IsLocalRing.maximalIdeal W := by rw [hWm]; exact Ideal.subset_span rfl
  have hqW : (q : W) ∈ IsLocalRing.maximalIdeal W := by
    have h1 : σ ϖ ^ (q - 1) = σ ε * (q : W) := by rw [← map_pow, hϖq, map_mul, map_natCast]
    have h2 : σ ε * (q : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← h1]; exact Ideal.pow_mem_of_mem _ hσϖ _ (by have := (Fact.out : q.Prime).two_le; omega)
    exact (Ideal.unit_mul_mem_iff_mem _ (hε.map σ)).mp h2

  have hQ := MvPowerSeries.isReduced_residueField_tensorProduct_quotient_span_C_mul_sub_mul_of_sub_drinfeldForm_mem_pow
    q W (σ ϖ) hWm hqW (σ ϖ) hσϖ f u v hu hf

  have eW := ((Algebra.TensorProduct.comm W (IsLocalRing.ResidueField W) (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})).toRingEquiv.trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}) (IsLocalRing.maximalIdeal W)).symm.toRingEquiv)
  have hJW : Ideal.map (algebraMap W (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})) (IsLocalRing.maximalIdeal W) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}) (MvPowerSeries.C (σ ϖ))} := by
    rw [hWm, Ideal.map_span, Set.image_singleton]
    rfl

  have hJR : Ideal.map (e : R →+* (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})) (Ideal.span {ι ϖ}) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u}) (MvPowerSeries.C (σ ϖ))} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact he ϖ
  have e2 := Ideal.quotientEquiv (Ideal.span {ι ϖ})
    (Ideal.map (algebraMap W (MvPowerSeries (Fin 2) W ⧸ Ideal.span {MvPowerSeries.C (σ ϖ) * v - f * u})) (IsLocalRing.maximalIdeal W)) e (by rw [hJR, hJW])
  haveI := hQ
  exact isReduced_of_injective (eW.symm.toRingHom.comp e2.toRingHom) (eW.symm.injective.comp e2.injective)

end S_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_isReduced_quotient_span_of_isRegularLocalRing_of_pow_sub_one_eq_mul_of_prime (solution)
