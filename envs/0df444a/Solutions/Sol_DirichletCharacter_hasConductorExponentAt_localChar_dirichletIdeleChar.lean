-- Prove2me | solution 1 for DirichletCharacter.hasConductorExponentAt_localChar_dirichletIdeleChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/0adb9d57-bb4a-5c1f-8820-e325f9e87503

import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open Rat.HeightOneSpectrum NumberField.AdelicLevel NumberField.TateGlobal LanglandsTunnell.TateLocal RatIdele

namespace LocalConductorExponent

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ

attribute [local instance] RatIdele.fact_prime_of_mem_primeFactors

private theorem absNorm_asIdeal_eq_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [asIdeal_eq_span_natGenerator v, Ideal.absNorm_span_singleton,
    show ((natGenerator v : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (natGenerator v : ℤ) from by simp,
    Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one,
    Int.natAbs_natCast]

private def emb (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) : (𝔸ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v u)

private theorem localChar_apply (μ : (𝔸ℚ)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletion ℚ)ˣ) :
    localChar μ v u = μ (emb v u) := rfl

private theorem coe_unitIntAt_emb_self (v : HeightOneSpectrum (𝓞 ℚ)) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    (unitIntAt v (emb v u) : v.adicCompletion ℚ) = u := by
  rw [coe_unitIntAt]
  exact unitAt_finIncl_localUnit_self v u hu

private theorem unitIntAt_emb_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) {u : (v.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    unitIntAt w (emb v u) = 1 := by
  refine Subtype.ext ?_
  rw [coe_unitIntAt, OneMemClass.coe_one]
  exact unitAt_finIncl_localUnit_of_ne v u hu hw

private abbrev plc (q : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) := (primesEquiv (R := 𝓞 ℚ)).symm q

private def padicEquiv (q : Nat.Primes) [Fact (q : ℕ).Prime] : (plc q).adicCompletionIntegers ℚ ≃+* ℤ_[q] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) q).symm.toAlgEquiv.toRingEquiv

private theorem unitPadicAt_eq (q : Nat.Primes) [Fact (q : ℕ).Prime] (x : (𝔸ℚ)ˣ) :
    unitPadicAt q x = padicEquiv q (unitIntAt (plc q) x) := rfl

private theorem valued_natCast (q : Nat.Primes) :
    Valued.v ((q : ℕ) : (plc q).adicCompletion ℚ) = exp (-1 : ℤ) := by
  have h := valuation_natGenerator (plc q)
  rw [natGenerator_primesEquiv_symm] at h
  rw [← map_natCast (algebraMap ℚ ((plc q).adicCompletion ℚ)), valued_algebraMap_rat]
  exact h

private theorem valued_natCast_pow (q : Nat.Primes) (m : ℕ) :
    Valued.v (((q : ℕ) : (plc q).adicCompletion ℚ) ^ m) = exp (-(m : ℤ)) := by
  induction m with
  | zero => rw [pow_zero, map_one, Nat.cast_zero, neg_zero, exp_zero]
  | succ m ih =>
    rw [pow_succ, map_mul, ih, valued_natCast, ← exp_add]
    congr 1
    omega

private theorem integers (v : HeightOneSpectrum (𝓞 ℚ)) :
    (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).Integers (v.adicCompletionIntegers ℚ) :=
  { hom_inj := fun _ _ h => Subtype.ext h
    map_le_one := fun x => x.2
    exists_of_le_one := fun x hx => ⟨⟨x, hx⟩, rfl⟩ }

private theorem pow_dvd_iff_valued_le (q : Nat.Primes) (x : (plc q).adicCompletionIntegers ℚ) (m : ℕ) :
    (((q : ℕ) : (plc q).adicCompletionIntegers ℚ)) ^ m ∣ x ↔
      Valued.v (x : (plc q).adicCompletion ℚ) ≤ exp (-(m : ℤ)) := by
  have key := (integers (plc q)).le_iff_dvd (x := x)
    (y := (((q : ℕ) : (plc q).adicCompletionIntegers ℚ)) ^ m)
  rw [map_pow, map_natCast, valued_natCast_pow] at key
  exact key.symm

private theorem pow_dvd_padicEquiv_iff (q : Nat.Primes) [Fact (q : ℕ).Prime] (x : (plc q).adicCompletionIntegers ℚ)
    (m : ℕ) :
    ((q : ℕ) : ℤ_[q]) ^ m ∣ padicEquiv q x ↔ (((q : ℕ) : (plc q).adicCompletionIntegers ℚ)) ^ m ∣ x := by
  constructor
  · intro h
    have := map_dvd (padicEquiv q).symm h
    rwa [map_pow, map_natCast, RingEquiv.symm_apply_apply] at this
  · intro h
    have := map_dvd (padicEquiv q) h
    rwa [map_pow, map_natCast] at this

private theorem toZModPow_eq_one_iff (q : Nat.Primes) [Fact (q : ℕ).Prime] {m : ℕ} {y : ℤ_[q]} :
    PadicInt.toZModPow m y = 1 ↔ ((q : ℕ) : ℤ_[q]) ^ m ∣ y - 1 := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

private theorem valued_eq_one_of_isUnit (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletionIntegers ℚ}
    (hx : IsUnit x) : Valued.v (x : v.adicCompletion ℚ) = 1 := by
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hx
  have h1 : Valued.v (x : v.adicCompletion ℚ) ≤ 1 := x.2
  have h2 : Valued.v (c : v.adicCompletion ℚ) ≤ 1 := c.2
  have h : Valued.v (x : v.adicCompletion ℚ) * Valued.v (c : v.adicCompletion ℚ) = 1 := by
    rw [← map_mul, ← MulMemClass.coe_mul, hc, OneMemClass.coe_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : ℤᵐ⁰) = Valued.v (x : v.adicCompletion ℚ) * Valued.v (c : v.adicCompletion ℚ) := h.symm
    _ ≤ Valued.v (x : v.adicCompletion ℚ) * 1 := mul_le_mul_right h2 _
    _ = Valued.v (x : v.adicCompletion ℚ) := mul_one _

variable {N : ℕ}

private theorem cast_cast_eq {d e : ℕ} (hd : d ∣ N) (he : e ∣ d) (z : ZMod N) :
    ZMod.castHom he (ZMod e) (ZMod.castHom hd (ZMod d) z) = ZMod.castHom (he.trans hd) (ZMod e) z :=
  RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom he (ZMod e)).comp (ZMod.castHom hd (ZMod d)))
    (ZMod.castHom (he.trans hd) (ZMod e))) z

private theorem castHom_eq_one_of_dvd {d e : ℕ} (hd : d ∣ N) (he : e ∣ d) {z : ZMod N}
    (hz : ZMod.castHom hd (ZMod d) z = 1) : ZMod.castHom (he.trans hd) (ZMod e) z = 1 := by
  rw [← cast_cast_eq hd he, hz, map_one]

variable [NeZero N]

private theorem equivPi_apply_eq_cast (z : ZMod N) (r : N.primeFactors) :
    ZMod.equivPi N (NeZero.ne N) z r
      = ZMod.castHom (Nat.ordProj_dvd N r) (ZMod ((r : ℕ) ^ N.factorization r)) z :=
  RingHom.congr_fun (RingHom.ext_zmod
    ((Pi.evalRingHom (fun r : N.primeFactors => ZMod ((r : ℕ) ^ N.factorization r)) r).comp
      (ZMod.equivPi N (NeZero.ne N)).toRingHom)
    (ZMod.castHom (Nat.ordProj_dvd N r) _)) z

variable (χ : DirichletCharacter ℂ N)

private theorem unitPadicAt_emb_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) {u : (w.adicCompletion ℚ)ˣ}
    (hu : Valued.v (u : w.adicCompletion ℚ) = 1) (r : ℕ) [hr : Fact r.Prime]
    (hrw : (primesEquiv (R := 𝓞 ℚ)).symm ⟨r, hr.out⟩ ≠ w) : unitPadicAt r (emb w u) = 1 := by
  unfold unitPadicAt
  rw [unitIntAt_emb_of_ne w hu hrw, map_one]

private theorem localChar_eq_one_of_mem (q : Nat.Primes) [Fact (q : ℕ).Prime] {u : ((plc q).adicCompletion ℚ)ˣ}
    (hu : u ∈ higherUnitsAt ℚ (plc q) (N.factorization q)) :
    localChar (DirichletCharacter.dirichletIdeleChar χ) (plc q) u = 1 := by
  rw [localChar_apply]
  have hu1 : Valued.v (u : (plc q).adicCompletion ℚ) = 1 := ((mem_higherUnitsAt_iff ℚ (plc q)).mp hu).1
  refine DirichletCharacter.dirichletIdeleChar_eq_one_of_unitResidue_eq_one χ ?_
  apply (ZMod.equivPi N (NeZero.ne N)).injective
  rw [equivPi_unitResidue, map_one]
  funext r
  rw [Pi.one_apply]
  show PadicInt.toZModPow (N.factorization r) (unitPadicAt r (emb (plc q) u)) = 1
  by_cases hr : (r : ℕ) = q
  · obtain ⟨r, _hrm⟩ := r
    dsimp only at hr
    subst hr
    show PadicInt.toZModPow (N.factorization q) (unitPadicAt q (emb (plc q) u)) = 1
    rw [unitPadicAt_eq, toZModPow_eq_one_iff, ← map_one (padicEquiv q), ← map_sub, pow_dvd_padicEquiv_iff,
      pow_dvd_iff_valued_le, AddSubgroupClass.coe_sub, OneMemClass.coe_one, coe_unitIntAt_emb_self (plc q) hu1]
    rcases ((mem_higherUnitsAt_iff ℚ (plc q)).mp hu).2 with h0 | hle
    · rw [h0, Nat.cast_zero, neg_zero, exp_zero]
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [hu1, map_one, max_self]
    · exact hle
  · have hne : (primesEquiv (R := 𝓞 ℚ)).symm ⟨r, (Fact.out : (r : ℕ).Prime)⟩ ≠ plc q := by
      intro h
      exact hr (congrArg (fun t : Nat.Primes => (t : ℕ)) ((primesEquiv (R := 𝓞 ℚ)).symm.injective h))
    rw [unitPadicAt_emb_of_ne (plc q) hu1 r hne, map_one]

private theorem exists_localChar_ne_one (hχ : χ.IsPrimitive) (q : Nat.Primes) [Fact (q : ℕ).Prime]
    (hq : (q : ℕ) ∣ N) {m : ℕ}
    (hm : m < N.factorization q) :
    ∃ u ∈ higherUnitsAt ℚ (plc q) m, localChar (DirichletCharacter.dirichletIdeleChar χ) (plc q) u ≠ 1 := by
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hpp : (q : ℕ).Prime := q.2
  have hN : N ≠ 0 := NeZero.ne N
  have ha0 : N.factorization q ≠ 0 := by omega
  have hma : m ≤ N.factorization q := hm.le
  have hd : N / q ∣ N := Nat.div_dvd_of_dvd hq
  have hpa : (q : ℕ) ^ N.factorization q ∣ N := Nat.ordProj_dvd N q
  have hNp : N / q * q = N := Nat.div_mul_cancel hq

  have hpa1 : (q : ℕ) ^ (N.factorization q - 1) ∣ N / q := by
    have h1 : (q : ℕ) ^ (N.factorization q - 1) * q = (q : ℕ) ^ N.factorization q := by
      rw [← pow_succ]
      congr 1
      omega
    have h2 : (q : ℕ) ^ (N.factorization q - 1) * q ∣ N / q * q := by
      rw [h1, hNp]
      exact hpa
    exact Nat.dvd_of_mul_dvd_mul_right hpp.pos h2
  have hpm : (q : ℕ) ^ m ∣ N / q := (pow_dvd_pow (q : ℕ) (by omega)).trans hpa1

  have hfac : χ.FactorsThrough (N / q) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hd]
    intro z hz
    rw [MonoidHom.mem_ker] at hz ⊢
    have hz1 : ZMod.castHom hd (ZMod (N / q)) (z : ZMod N) = 1 := by
      have := congrArg Units.val hz
      rwa [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at this

    obtain ⟨zp, hzp⟩ : ∃ zp : ZMod ((q : ℕ) ^ N.factorization q),
        zp = ZMod.castHom hpa (ZMod ((q : ℕ) ^ N.factorization q)) (z : ZMod N) := ⟨_, rfl⟩
    haveI : NeZero ((q : ℕ) ^ N.factorization q) := ⟨pow_ne_zero _ hpp.ne_zero⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = zp.val := ⟨_, rfl⟩
    have hnzp : ((n : ℕ) : ZMod ((q : ℕ) ^ N.factorization q)) = zp := by
      rw [hn]
      exact ZMod.natCast_zmod_val zp
    have hzpu : IsUnit zp := by
      rw [hzp]
      exact ZMod.isUnit_cast_of_dvd hpa z
    have hncop : n.Coprime q := by
      have : IsUnit ((n : ℕ) : ZMod ((q : ℕ) ^ N.factorization q)) := by
        rw [hnzp]
        exact hzpu
      rw [ZMod.isUnit_iff_coprime] at this
      exact (Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero ha0) n q).mp this
    have hyu : IsUnit ((n : ℕ) : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact hncop.symm
    have hya : PadicInt.toZModPow (N.factorization q) ((n : ℕ) : ℤ_[q]) = zp := by
      rw [map_natCast, hnzp]
    have hym : PadicInt.toZModPow m ((n : ℕ) : ℤ_[q]) = 1 := by
      rw [← PadicInt.cast_toZModPow m (N.factorization q) hma, hya, hzp,
        ← ZMod.castHom_apply (R := ZMod ((q : ℕ) ^ m)) (h := pow_dvd_pow (q : ℕ) hma),
        cast_cast_eq hpa (pow_dvd_pow (q : ℕ) hma)]
      exact castHom_eq_one_of_dvd hd hpm hz1

    obtain ⟨uO, huO⟩ : ∃ uO : (plc q).adicCompletionIntegers ℚ, uO = (padicEquiv q).symm ((n : ℕ) : ℤ_[q]) :=
      ⟨_, rfl⟩
    have huOu : IsUnit uO := by
      rw [huO]
      exact hyu.map (padicEquiv q).symm
    have hval : Valued.v (uO : (plc q).adicCompletion ℚ) = 1 := valued_eq_one_of_isUnit (plc q) huOu
    have hne0 : (uO : (plc q).adicCompletion ℚ) ≠ 0 := fun h => by
      rw [h, map_zero] at hval
      exact zero_ne_one hval
    obtain ⟨u, hucoe⟩ : ∃ u : ((plc q).adicCompletion ℚ)ˣ, (u : (plc q).adicCompletion ℚ) = uO :=
      ⟨Units.mk0 _ hne0, rfl⟩
    have hu1 : Valued.v (u : (plc q).adicCompletion ℚ) = 1 := by
      rw [hucoe]
      exact hval

    have humem : u ∈ higherUnitsAt ℚ (plc q) m := by
      refine (mem_higherUnitsAt_iff ℚ (plc q)).mpr ⟨hu1, Or.inr ?_⟩
      have hdvd : ((q : ℕ) : ℤ_[q]) ^ m ∣ padicEquiv q (uO - 1) := by
        rw [map_sub, map_one, huO, RingEquiv.apply_symm_apply]
        exact (toZModPow_eq_one_iff q).mp hym
      rw [pow_dvd_padicEquiv_iff, pow_dvd_iff_valued_le, AddSubgroupClass.coe_sub, OneMemClass.coe_one] at hdvd
      rwa [hucoe]

    have hint : unitIntAt (plc q) (emb (plc q) u) = uO :=
      Subtype.ext ((coe_unitIntAt_emb_self (plc q) hu1).trans hucoe)
    have hres : unitResidue N (emb (plc q) u) = (z : ZMod N) := by
      apply (ZMod.equivPi N (NeZero.ne N)).injective
      rw [equivPi_unitResidue]
      funext r
      rw [equivPi_apply_eq_cast]
      show PadicInt.toZModPow (N.factorization r) (unitPadicAt r (emb (plc q) u)) = _
      by_cases hr : (r : ℕ) = q
      · obtain ⟨r, _hrm⟩ := r
        dsimp only at hr
        subst hr
        show PadicInt.toZModPow (N.factorization q) (unitPadicAt q (emb (plc q) u))
          = ZMod.castHom hpa (ZMod ((q : ℕ) ^ N.factorization q)) (z : ZMod N)
        rw [unitPadicAt_eq, hint, huO, RingEquiv.apply_symm_apply, hya, hzp]
      · have hne : (primesEquiv (R := 𝓞 ℚ)).symm ⟨r, (Fact.out : (r : ℕ).Prime)⟩ ≠ plc q := by
          intro h
          exact hr (congrArg (fun t : Nat.Primes => (t : ℕ)) ((primesEquiv (R := 𝓞 ℚ)).symm.injective h))
        rw [unitPadicAt_emb_of_ne (plc q) hu1 r hne, map_one]

        have hrp : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.2
        have hcop : ((r : ℕ) ^ N.factorization r).Coprime q :=
          Nat.Coprime.pow_left _ ((Nat.coprime_primes hrp hpp).mpr hr)
        have hrd : (r : ℕ) ^ N.factorization r ∣ N / q :=
          hcop.dvd_of_dvd_mul_right (by rw [hNp]; exact Nat.ordProj_dvd N r)
        exact (castHom_eq_one_of_dvd hd hrd hz1).symm

    have h1 := hcon u humem
    rw [localChar_apply] at h1
    have h2 := congrArg (fun t : ℂˣ => (t : ℂ)) h1
    simp only [DirichletCharacter.coe_dirichletIdeleChar_apply, Units.val_one, inv_eq_one] at h2
    rw [hres] at h2
    exact Units.ext (by rw [MulChar.coe_toUnitHom, Units.val_one]; exact h2)

  have hcd : χ.conductor ∣ N / q := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd (χ := χ) hd).mp hfac
  have hc : χ.conductor = N := hχ
  rw [hc] at hcd
  have hlt : N / q < N := Nat.div_lt_self (Nat.pos_of_ne_zero hN) hpp.one_lt
  have hpos : 0 < N / q := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hq) hpp.pos
  exact absurd (Nat.le_of_dvd hpos hcd) (not_le.mpr hlt)

private theorem main (hχ : χ.IsPrimitive) (q : Nat.Primes) [Fact (q : ℕ).Prime] :
    HasConductorExponentAt ℚ (plc q) (localChar (DirichletCharacter.dirichletIdeleChar χ) (plc q))
      (N.factorization q) := by
  by_cases hq : (q : ℕ) ∣ N
  · exact ⟨fun u hu => localChar_eq_one_of_mem χ q hu, fun m hm => exists_localChar_ne_one χ hχ q hq hm⟩
  · rw [Nat.factorization_eq_zero_of_not_dvd hq, hasConductorExponentAt_zero_iff]
    intro u hu
    rw [localChar_apply]
    have hq' : ¬ natGenerator (plc q) ∣ N := by rwa [natGenerator_primesEquiv_symm]
    exact DirichletCharacter.dirichletIdeleChar_finIncl_localUnit_of_valued_one χ hq' u hu

end LocalConductorExponent

open LocalConductorExponent DirichletCharacter in

theorem solution
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    HasConductorExponentAt ℚ v (localChar (dirichletIdeleChar χ) v)
      (N.factorization (Ideal.absNorm v.asIdeal)) := by
  obtain ⟨q, rfl⟩ : ∃ q : Nat.Primes, v = (primesEquiv (R := 𝓞 ℚ)).symm q :=
    ⟨primesEquiv v, ((primesEquiv (R := 𝓞 ℚ)).symm_apply_apply v).symm⟩
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [LocalConductorExponent.absNorm_asIdeal_eq_natGenerator, natGenerator_primesEquiv_symm]
  exact LocalConductorExponent.main χ hχ q

end

end S_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar
end P2MW
export P2MW.S_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar (solution)
