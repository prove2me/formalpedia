-- Prove2me | solution 1 for CuspForm.exists_isNewform_of_point_of_isUnit_up
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/627f8991-0eca-5082-83f5-e0918356975a

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_annihilator_le_of_isPrime
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Theorems.Thm_CuspForm_exists_isNewform_descent
import Theorems.Thm_CuspForm_exists_qCoeff_eq_sum_divisors_of_isNewform_matching
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isNewform_of_point_of_isUnit_up
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

namespace OrdPtNFU

open ModularFormClass

section SatLift

variable {T B O : Type*} [CommRing T] [CommRing B] [CommRing O]

def satRange (lam : T →+* B) (U : T) : Subring B where
  carrier := {z | ∃ (k : ℕ) (t : T), lam U ^ k * z = lam t}
  mul_mem' := by
    rintro z w ⟨k, t, ht⟩ ⟨m, s, hs⟩
    refine ⟨k + m, t * s, ?_⟩
    rw [map_mul, ← ht, ← hs]; ring
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro z w ⟨k, t, ht⟩ ⟨m, s, hs⟩
    refine ⟨k + m, U ^ m * t + U ^ k * s, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ht, ← hs]; ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro z ⟨k, t, ht⟩
    exact ⟨k, -t, by rw [map_neg, ← ht]; ring⟩

theorem mem_satRange_iff {lam : T →+* B} {U : T} {z : B} :
    z ∈ satRange lam U ↔ ∃ (k : ℕ) (t : T), lam U ^ k * z = lam t := Iff.rfl

theorem mem_satRange_of_eq {lam : T →+* B} {U : T} {z : B} (t : T) (h : z = lam t) :
    z ∈ satRange lam U := ⟨0, t, by rw [pow_zero, one_mul, h]⟩

variable {lam : T →+* B} {chi : T →+* O} {U : T} {v : O}

theorem lift_wd (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1)
    {z : B} {k m : ℕ} {t s : T} (ht : lam U ^ k * z = lam t) (hs : lam U ^ m * z = lam s) :
    chi t * v ^ k = chi s * v ^ m := by
  have h1 : lam (U ^ m * t - U ^ k * s) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, ← ht, ← hs]; ring
  have h2 := hker _ h1
  rw [map_sub, map_mul, map_mul, map_pow, map_pow, sub_eq_zero] at h2
  calc chi t * v ^ k = chi t * v ^ k * (chi U * v) ^ m := by rw [hv, one_pow, mul_one]
    _ = chi U ^ m * chi t * v ^ (k + m) := by ring
    _ = chi U ^ k * chi s * v ^ (k + m) := by rw [h2]
    _ = chi s * v ^ m * (chi U * v) ^ k := by ring
    _ = chi s * v ^ m := by rw [hv, one_pow, mul_one]

noncomputable def lift (chi₀ : T →+* O) (v₀ : O) (z : satRange lam U) : O :=
  chi₀ (mem_satRange_iff.mp z.2).choose_spec.choose * v₀ ^ (mem_satRange_iff.mp z.2).choose

theorem lift_eq (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1)
    (z : satRange lam U) {k : ℕ} {t : T} (h : lam U ^ k * (z : B) = lam t) :
    lift chi v z = chi t * v ^ k :=
  lift_wd hker hv (mem_satRange_iff.mp z.2).choose_spec.choose_spec h

noncomputable def liftHom (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1) :
    satRange lam U →+* O where
  toFun := lift chi v
  map_one' := by
    rw [lift_eq hker hv 1 (k := 0) (t := 1) (by simp)]; simp
  map_mul' z w := by
    obtain ⟨k, t, ht⟩ := mem_satRange_iff.mp z.2
    obtain ⟨m, s, hs⟩ := mem_satRange_iff.mp w.2
    have hzw : lam U ^ (k + m) * ((z * w : satRange lam U) : B) = lam (t * s) := by
      rw [Subring.coe_mul, map_mul, ← ht, ← hs]; ring
    rw [lift_eq hker hv z ht, lift_eq hker hv w hs, lift_eq hker hv (z * w) hzw, map_mul]; ring
  map_zero' := by
    rw [lift_eq hker hv 0 (k := 0) (t := 0) (by simp)]; simp
  map_add' z w := by
    obtain ⟨k, t, ht⟩ := mem_satRange_iff.mp z.2
    obtain ⟨m, s, hs⟩ := mem_satRange_iff.mp w.2
    have hzw : lam U ^ (k + m) * ((z + w : satRange lam U) : B) = lam (U ^ m * t + U ^ k * s) := by
      rw [Subring.coe_add, map_add, map_mul, map_mul, map_pow, map_pow, ← ht, ← hs]; ring
    rw [lift_eq hker hv z ht, lift_eq hker hv w hs, lift_eq hker hv (z + w) hzw, map_add, map_mul,
      map_mul, map_pow, map_pow]
    calc (chi U ^ m * chi t + chi U ^ k * chi s) * v ^ (k + m)
        = chi t * v ^ k * (chi U * v) ^ m + chi s * v ^ m * (chi U * v) ^ k := by ring
      _ = chi t * v ^ k + chi s * v ^ m := by simp only [hv, one_pow, mul_one]

theorem liftHom_apply_of_eq (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1)
    (z : satRange lam U) (t : T) (h : (z : B) = lam t) : liftHom hker hv z = chi t := by
  change lift chi v z = chi t
  rw [lift_eq hker hv z (k := 0) (t := t) (by rw [pow_zero, one_mul, h]), pow_zero, mul_one]

theorem liftHom_apply_of_mul_eq (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1)
    (z : satRange lam U) (t : T) (h : lam U * (z : B) = lam t) : liftHom hker hv z = chi t * v := by
  change lift chi v z = chi t * v
  rw [lift_eq hker hv z (k := 1) (t := t) (by rw [pow_one, h]), pow_one]

theorem map_mul_add_natCast (f : T →+* B) (x : T) (n : ℕ) : f (x * x + n) = f x * f x + n := by
  simp

theorem liftHom_inclusion_apply (hker : ∀ t : T, lam t = 0 → chi t = 0) (hv : chi U * v = 1)
    {T₂ : Type*} [CommRing T₂] {chig : T₂ →+* B} (hle : chig.range ≤ satRange lam U)
    (t : T₂) (s : T) (h : chig t = lam s) :
    liftHom hker hv (Subring.inclusion hle (chig.rangeRestrict t)) = chi s := by
  apply liftHom_apply_of_eq hker hv
  exact h

theorem liftHom_inclusion_apply_of_mul (hker : ∀ t : T, lam t = 0 → chi t = 0)
    (hv : chi U * v = 1) {T₂ : Type*} [CommRing T₂] {chig : T₂ →+* B}
    (hle : chig.range ≤ satRange lam U) (t : T₂) (s : T) (h : lam U * chig t = lam s) :
    liftHom hker hv (Subring.inclusion hle (chig.rangeRestrict t)) = chi s * v := by
  apply liftHom_apply_of_mul_eq hker hv
  exact h

end SatLift

set_option maxHeartbeats 3200000 in
theorem range_subset {M : ℕ} [NeZero M] (S' : Set ℕ) (chig : CuspForm.heckeAlgebra M 2 S' →+* ℂ)
    (L : Subring ℂ)
    (hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ S'),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) ∈ L)
    (hU : ∀ (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) (hqS : q ∉ S'),
      chig (CuspForm.heckeAlgebra.U hq hqM hqS) ∈ L) :
    ∀ t : CuspForm.heckeAlgebra M 2 S', chig t ∈ L := by
  rintro ⟨x, hx⟩
  refine Algebra.adjoin_induction (R := ℤ) (s := CuspForm.heckeGenerators M 2 S')
    (p := fun x hx => chig ⟨x, hx⟩ ∈ L) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨ℓ, hℓ, hℓM, hℓS, rfl⟩ | ⟨q, hqM, hq, hqS, rfl⟩)
    · exact hT ℓ hℓ hℓM hℓS
    · exact hU q hq hqM hqS
  · intro r
    have e : ∀ h : algebraMap ℤ _ r ∈ CuspForm.heckeAlgebra M 2 S',
        chig ⟨algebraMap ℤ _ r, h⟩ = (r : ℂ) := fun h =>
      RingHom.congr_fun (RingHom.eq_intCast' (chig.comp (Int.castRingHom _))) r
    show chig ⟨algebraMap ℤ _ r, _⟩ ∈ L
    rw [e]
    exact intCast_mem L r
  · intro x y hx hy ihx ihy
    change chig (⟨x, hx⟩ + ⟨y, hy⟩) ∈ L
    rw [chig.map_add]
    exact add_mem ihx ihy
  · intro x y hx hy ihx ihy
    change chig (⟨x, hx⟩ * ⟨y, hy⟩) ∈ L
    rw [chig.map_mul]
    exact mul_mem ihx ihy

theorem qCoeff_ppow_of_dvd {N : ℕ} {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    ∀ j : ℕ, qCoeff f (p ^ j) = qCoeff f p ^ j
  | 0 => by rw [pow_zero, pow_zero, hf.qCoeff_one]
  | 1 => by rw [pow_one, pow_one]
  | (j + 2) => by
    rw [hf.qCoeff_prime_pow_of_dvd p j hp hpN, qCoeff_ppow_of_dvd hf hp hpN (j + 1)]; ring

theorem dvd_pow_of_dvd_pow {D p d : ℕ} (hp : p.Prime) (hD : D ≠ 0) (hdD : d ∣ D) (m : ℕ)
    (h : d ∣ p ^ m) : d ∣ p ^ D := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp h
  have h1 : p ^ i ≤ D := Nat.le_of_dvd (Nat.pos_of_ne_zero hD) hdD
  have h2 : i < p ^ i := Nat.lt_pow_self hp.one_lt
  exact pow_dvd_pow p (by omega)

theorem old_of_divisor_sum {D p : ℕ} (hp : p.Prime) (hD : D ≠ 0) {af ag c : ℕ → ℂ} {u a : ℂ}
    (hc : ∀ n, af n = ∑ d ∈ D.divisors, c d * (if d ∣ n then ag (n / d) else 0))
    (hf : ∀ j, af (p ^ j) = u ^ j)
    (hg : ∀ r, ag (p ^ (r + 2)) = a * ag (p ^ (r + 1)) - p * ag (p ^ r)) :
    u ^ D * (u ^ 2 - a * u + p) = 0 := by
  have key : ∀ d ∈ D.divisors,
      c d * (if d ∣ p ^ (D + 2) then ag (p ^ (D + 2) / d) else 0)
        - a * (c d * (if d ∣ p ^ (D + 1) then ag (p ^ (D + 1) / d) else 0))
        + p * (c d * (if d ∣ p ^ D then ag (p ^ D / d) else 0)) = 0 := by
    intro d hd
    have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
    by_cases hδ : d ∣ p ^ D
    · obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hδ
      have h2 : p ^ i ∣ p ^ (D + 2) := pow_dvd_pow p (by omega)
      have h1 : p ^ i ∣ p ^ (D + 1) := pow_dvd_pow p (by omega)
      rw [if_pos h2, if_pos h1, if_pos hδ, Nat.pow_div (by omega) hp.pos,
        Nat.pow_div (by omega) hp.pos, Nat.pow_div hi hp.pos,
        show D + 2 - i = (D - i) + 2 by omega, show D + 1 - i = (D - i) + 1 by omega, hg (D - i)]
      ring
    · have h2 : ¬ d ∣ p ^ (D + 2) := fun h => hδ (dvd_pow_of_dvd_pow hp hD hdD _ h)
      have h1 : ¬ d ∣ p ^ (D + 1) := fun h => hδ (dvd_pow_of_dvd_pow hp hD hdD _ h)
      rw [if_neg h2, if_neg h1, if_neg hδ]; ring
  calc u ^ D * (u ^ 2 - a * u + p) = u ^ (D + 2) - a * u ^ (D + 1) + p * u ^ D := by ring
    _ = af (p ^ (D + 2)) - a * af (p ^ (D + 1)) + p * af (p ^ D) := by rw [hf, hf, hf]
    _ = _ := by rw [hc (p ^ (D + 2)), hc (p ^ (D + 1)), hc (p ^ D)]
    _ = ∑ d ∈ D.divisors, (c d * (if d ∣ p ^ (D + 2) then ag (p ^ (D + 2) / d) else 0)
        - a * (c d * (if d ∣ p ^ (D + 1) then ag (p ^ (D + 1) / d) else 0))
        + p * (c d * (if d ∣ p ^ D then ag (p ^ D / d) else 0))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    _ = 0 := Finset.sum_eq_zero key

theorem new_of_divisor_sum {D p : ℕ} (hp : p.Prime) (hD : D ≠ 0) {af ag c : ℕ → ℂ} {u a : ℂ}
    (hc : ∀ n, af n = ∑ d ∈ D.divisors, c d * (if d ∣ n then ag (n / d) else 0))
    (hf : ∀ j, af (p ^ j) = u ^ j)
    (hg : ∀ r, ag (p ^ (r + 1)) = a * ag (p ^ r)) :
    u ^ D * (u - a) = 0 := by
  have key : ∀ d ∈ D.divisors,
      c d * (if d ∣ p ^ (D + 1) then ag (p ^ (D + 1) / d) else 0)
        - a * (c d * (if d ∣ p ^ D then ag (p ^ D / d) else 0)) = 0 := by
    intro d hd
    have hdD : d ∣ D := Nat.dvd_of_mem_divisors hd
    by_cases hδ : d ∣ p ^ D
    · obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hδ
      have h1 : p ^ i ∣ p ^ (D + 1) := pow_dvd_pow p (by omega)
      rw [if_pos h1, if_pos hδ, Nat.pow_div (by omega) hp.pos, Nat.pow_div hi hp.pos,
        show D + 1 - i = (D - i) + 1 by omega, hg (D - i)]
      ring
    · have h1 : ¬ d ∣ p ^ (D + 1) := fun h => hδ (dvd_pow_of_dvd_pow hp hD hdD _ h)
      rw [if_neg h1, if_neg hδ]; ring
  calc u ^ D * (u - a) = u ^ (D + 1) - a * u ^ D := by ring
    _ = af (p ^ (D + 1)) - a * af (p ^ D) := by rw [hf, hf]
    _ = _ := by rw [hc (p ^ (D + 1)), hc (p ^ D)]
    _ = ∑ d ∈ D.divisors, (c d * (if d ∣ p ^ (D + 1) then ag (p ^ (D + 1) / d) else 0)
        - a * (c d * (if d ∣ p ^ D then ag (p ^ D / d) else 0))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = 0 := Finset.sum_eq_zero key

end OrdPtNFU

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open OrdPtNFU ModularFormClass in
theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Finset ℕ)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪']
    (χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪')
    (hpN : p ∣ N) (up : 𝒪')
    (hup : ∃ χ' : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p}) →+* 𝒪',
      (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
        χ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono Set.diff_subset) t) = χ t) ∧
      χ' (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN (by simp)) = up)
    (hunit : IsUnit up) :
    ∃ (Mg : ℕ) (_ : NeZero Mg) (hMgN : Mg ∣ N)
      (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (_ : g.IsNewform)
      (chig : CuspForm.heckeAlgebra Mg 2 ((↑S : Set ℕ) \ {p}) →+* ℂ)
      (_ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) = ModularFormClass.qCoeff g ℓ)
      (iota : chig.range →+* 𝒪'),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
        iota (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ
          (fun h => hℓN (h.trans hMgN)) (fun h => hℓS (Set.mem_of_mem_diff h)))) =
          χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ((∃ hpMg : ¬ p ∣ Mg,
          up * up - iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpMg (by simp))) * up + (p : 𝒪') = 0) ∨
       (∃ hpMg : p ∣ Mg, ¬ p ^ 2 ∣ Mg ∧
          iota (chig.rangeRestrict
            (CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpMg (by simp))) = up)) := by
  obtain ⟨χ', hχ'χ, hχ'U⟩ := hup
  have hp : p.Prime := Fact.out
  have hpS' : p ∉ ((↑S : Set ℕ) \ {p}) := by simp

  have hdiff : ∀ {ℓ : ℕ}, ℓ ∉ (↑S : Set ℕ) → ℓ ∉ ((↑S : Set ℕ) \ {p}) :=
    fun hℓS h => hℓS (Set.mem_of_mem_diff h)
  have hndvd : ∀ {ℓ : ℕ}, ℓ.Prime → ℓ ∉ (↑S : Set ℕ) → ¬ ℓ ∣ N :=
    fun hℓ hℓS h => hℓS (Finset.mem_coe.mpr (hNS _ hℓ h))

  obtain ⟨f', hf', hann⟩ := CuspForm.exists_isNormalizedEigenform_annihilator_le_of_isPrime
    ((↑S : Set ℕ) \ {p}) (RingHom.ker χ') (RingHom.ker_isPrime χ')

  obtain ⟨lam, hlam, hlamT, hlamU⟩ := hf'.exists_ringHom_heckeAlgebra ((↑S : Set ℕ) \ {p})
  have hker : ∀ t, lam t = 0 → χ' t = 0 := fun t ht => by
    have h0 : (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) f' = 0 := by
      rw [hlam t, ht, zero_smul]
    exact RingHom.mem_ker.mp (hann t h0)

  set U : CuspForm.heckeAlgebra N 2 ((↑S : Set ℕ) \ {p}) :=
    CuspForm.heckeAlgebra.U (Fact.out : p.Prime) hpN hpS'
  have hχU : χ' U = up := hχ'U
  have hlU : lam U = qCoeff f' p := hlamU p hp hpN hpS'
  obtain ⟨v, huv⟩ := hunit.exists_right_inv
  have hv : χ' U * v = 1 := by rw [hχU]; exact huv
  have hu0 : qCoeff f' p ≠ 0 := fun h0 => by
    have h1 : χ' U = 0 := hker U (by rw [hlU, h0])
    rw [hχU] at h1
    exact not_isUnit_zero (h1 ▸ hunit)

  obtain ⟨Mg, hMgN, g, hg, hmatch⟩ := CuspForm.exists_isNewform_descent f' hf'
  haveI hMg0 : NeZero Mg := ⟨fun h => NeZero.ne N (Nat.eq_zero_of_zero_dvd (h ▸ hMgN))⟩
  have hgN : g.IsNormalizedEigenform := hg.isNormalizedEigenform

  obtain ⟨c, hc⟩ := CuspForm.exists_qCoeff_eq_sum_divisors_of_isNewform_matching Mg N hMgN g hg
    f' hf' (fun ℓ hℓ hℓN => hmatch ℓ hℓ hℓN)
  have hD0 : N / Mg ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hMgN)
      (Nat.pos_of_ne_zero (NeZero.ne Mg))).ne'
  have hfpow : ∀ j, qCoeff f' (p ^ j) = qCoeff f' p ^ j := qCoeff_ppow_of_dvd hf' hp hpN

  obtain ⟨chig, -, hchigT, hchigU⟩ := hgN.exists_ringHom_heckeAlgebra ((↑S : Set ℕ) \ {p})

  have hTval : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      ℓ ≠ p → ∃ hℓN : ¬ ℓ ∣ N,
        chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) = lam (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) := by
    intro ℓ hℓ hℓMg hℓS hℓp
    have hℓS0 : ℓ ∉ (↑S : Set ℕ) := fun h => hℓS ⟨h, hℓp⟩
    refine ⟨hndvd hℓ hℓS0, ?_⟩
    rw [hchigT, hmatch ℓ hℓ (hndvd hℓ hℓS0), hlamT]

  let L : Subring ℂ := satRange lam U
  have hLT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMg : ¬ ℓ ∣ Mg) (hℓS : ℓ ∉ ((↑S : Set ℕ) \ {p})),
      ℓ ≠ p → chig (CuspForm.heckeAlgebra.T hℓ hℓMg hℓS) ∈ L := by
    intro ℓ hℓ hℓMg hℓS hℓp
    obtain ⟨hℓN, h⟩ := hTval ℓ hℓ hℓMg hℓS hℓp
    exact mem_satRange_of_eq _ h
  by_cases hpMg : p ∣ Mg
  ·
    have hgpow : ∀ j, qCoeff g (p ^ j) = qCoeff g p ^ j := qCoeff_ppow_of_dvd hgN hp hpMg
    have hroot := new_of_divisor_sum (af := qCoeff f') (ag := qCoeff g) (u := qCoeff f' p)
      (a := qCoeff g p) hp hD0 hc hfpow (fun r => by rw [hgpow, hgpow]; ring)
    have hua : qCoeff g p = qCoeff f' p := by
      have := (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hu0)
      exact (sub_eq_zero.mp this).symm
    have hp2 : ¬ p ^ 2 ∣ Mg := fun h =>
      hu0 (hua.symm.trans (CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg p hp h))

    have hUval : chig (CuspForm.heckeAlgebra.U hp hpMg hpS') = lam U := by
      rw [hchigU, hua, hlU]
    have hle : chig.range ≤ L := by
      rintro _ ⟨t, rfl⟩
      refine range_subset _ chig L (fun ℓ hℓ hℓMg hℓS => ?_) (fun q hq hqMg hqS => ?_) t
      · exact hLT ℓ hℓ hℓMg hℓS (fun h => hℓMg (h ▸ hpMg))
      · have hpq : p = q := by
          by_contra hpq
          exact hqS ⟨Finset.mem_coe.mpr (hNS q hq (hqMg.trans hMgN)), fun h => hpq h.symm⟩
        subst hpq
        exact mem_satRange_of_eq _ hUval
    refine ⟨Mg, hMg0, hMgN, g, hg, chig, hchigT, (liftHom hker hv).comp (Subring.inclusion hle),
      fun ℓ hℓ hℓN hℓS => ?_, Or.inr ⟨hpMg, hp2, ?_⟩⟩
    · have hℓp : ℓ ≠ p := fun h => hℓN (h ▸ hpN)
      obtain ⟨hℓN', h⟩ := hTval ℓ hℓ (fun h => hℓN (h.trans hMgN)) (hdiff hℓS) hℓp
      rw [RingHom.comp_apply, liftHom_inclusion_apply hker hv hle _ _ h, ← hχ'χ]
      exact congrArg _ (Subtype.ext rfl)
    · rw [RingHom.comp_apply, liftHom_inclusion_apply hker hv hle _ U hUval, hχU]
  ·
    have hroot := old_of_divisor_sum (af := qCoeff f') (ag := qCoeff g) (u := qCoeff f' p)
      (a := qCoeff g p) hp hD0 hc hfpow (fun r => hgN.qCoeff_prime_pow_of_not_dvd p r hp hpMg)
    have hquad : qCoeff f' p ^ 2 - qCoeff g p * qCoeff f' p + p = 0 :=
      (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hu0)

    have hTp : lam U * chig (CuspForm.heckeAlgebra.T hp hpMg hpS') = lam (U * U + (p : _)) := by
      rw [hchigT, map_mul_add_natCast, hlU]
      linear_combination -hquad
    have hle : chig.range ≤ L := by
      rintro _ ⟨t, rfl⟩
      refine range_subset _ chig L (fun ℓ hℓ hℓMg hℓS => ?_) (fun q hq hqMg hqS => ?_) t
      · by_cases hpℓ : p = ℓ
        · subst hpℓ
          exact ⟨1, U * U + (p : _), by rw [pow_one]; exact hTp⟩
        · exact hLT ℓ hℓ hℓMg hℓS (fun h => hpℓ h.symm)
      · exfalso
        have hqp : q ≠ p := fun h => hpMg (h ▸ hqMg)
        exact hqS ⟨Finset.mem_coe.mpr (hNS q hq (hqMg.trans hMgN)), hqp⟩
    refine ⟨Mg, hMg0, hMgN, g, hg, chig, hchigT, (liftHom hker hv).comp (Subring.inclusion hle),
      fun ℓ hℓ hℓN hℓS => ?_, Or.inl ⟨hpMg, ?_⟩⟩
    · have hℓp : ℓ ≠ p := fun h => hℓN (h ▸ hpN)
      obtain ⟨hℓN', h⟩ := hTval ℓ hℓ (fun h => hℓN (h.trans hMgN)) (hdiff hℓS) hℓp
      rw [RingHom.comp_apply, liftHom_inclusion_apply hker hv hle _ _ h, ← hχ'χ]
      exact congrArg _ (Subtype.ext rfl)
    · rw [RingHom.comp_apply, liftHom_inclusion_apply_of_mul hker hv hle _ (U * U + (p : _)) hTp,
        map_mul_add_natCast, hχU]
      linear_combination (-(up * up + (p : 𝒪'))) * huv

end S_CuspForm_exists_isNewform_of_point_of_isUnit_up
end P2MW
export P2MW.S_CuspForm_exists_isNewform_of_point_of_isUnit_up (solution)
