-- Prove2me | solution 1 for ExtCitation.Cyclotomic.unitsOmegaEigenvector_two_eq_zero_of_local_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dc6f8792-16e2-526b-8ea0-cd773edad9ad

import Definitions.Def_ExtCitation_CyclotomicUnits
import Theorems.Thm_ExtCitation_Cyclotomic_finrank_unitsOmegaEigenspace_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow

set_option autoImplicit false

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "unitsEnd unitsEnd_proj unitsGalAction unitsOmegaEigenspace omegaIdempotent finrank_unitsOmegaEigenspace_two"
namespace B2Con
p2m_open "ExtCitation.Cyclotomic ExtCitation"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero Finset

private lemma zm0_eq_one_of_pow_eq_one {x : ℤᵐ⁰} (hx : x ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n = 1) : x = 1 := by
  rw [← exp_log hx, ← exp_nsmul, ← exp_zero, exp_inj] at h
  rw [← exp_log hx, ← exp_zero, exp_inj]
  have h' : (n : ℤ) * x.log = 0 := by rw [← nsmul_eq_mul]; exact h
  exact (mul_eq_zero.mp h').resolve_left (Int.natCast_ne_zero.mpr hn)

private lemma zm0_le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (h : x < 1) : x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · rw [← exp_log hx, ← exp_zero, exp_lt_exp] at h
    rw [← exp_log hx, exp_le_exp]
    omega

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem pow_sub_one_mem_pow_three_of_local_pow
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (𝔭 : HeightOneSpectrum R) (u : Rˣ)
    (hz1 : (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal)
    (hp2 : (p : R) ∈ 𝔭.asIdeal ^ 2)
    (hloc : ∃ v : (𝔭.adicCompletion K)ˣ,
      v ^ p = Units.map (algebraMap R (𝔭.adicCompletion K)).toMonoidHom u) :
    (u : R) ^ (p - 1) - 1 ∈ 𝔭.asIdeal ^ 3 := by
  obtain ⟨v, hv⟩ := hloc

  have hwR : ∀ r : R, Valued.v ((algebraMap R (𝔭.adicCompletion K)) r)
      = 𝔭.intValuation r := by
    intro r
    have h1 : (algebraMap R (𝔭.adicCompletion K)) r = ((algebraMap R K r : K) :
        𝔭.adicCompletion K) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]

  have hu1 : 𝔭.intValuation (u : R) = 1 := by
    refine le_antisymm (intValuation_le_one 𝔭 _) ?_
    have humul : 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) = 1 := by
      rw [← Valuation.map_mul, Units.mul_inv, Valuation.map_one]
    calc (1 : ℤᵐ⁰) = 𝔭.intValuation (u : R) * 𝔭.intValuation ((u⁻¹ : Rˣ) : R) :=
          humul.symm
    _ ≤ 𝔭.intValuation (u : R) * 1 :=
          mul_le_mul' le_rfl (intValuation_le_one 𝔭 _)
    _ = 𝔭.intValuation (u : R) := mul_one _
  have hwu : Valued.v ((algebraMap R (𝔭.adicCompletion K)) (u : R)) = 1 := by
    rw [hwR]; exact hu1

  have hv' : (v : 𝔭.adicCompletion K) ^ p
      = (algebraMap R (𝔭.adicCompletion K)) (u : R) := by
    have h0 := congrArg Units.val hv
    simpa using h0
  have hwv : Valued.v (v : 𝔭.adicCompletion K) = 1 := by
    have hpow : (Valued.v (v : 𝔭.adicCompletion K)) ^ p = 1 := by
      rw [← map_pow, hv', hwu]
    have hne : Valued.v (v : 𝔭.adicCompletion K) ≠ 0 := by
      simp
    exact zm0_eq_one_of_pow_eq_one hne hp.ne_zero hpow

  set y : 𝔭.adicCompletion K := (v : 𝔭.adicCompletion K) ^ (p - 1) with hy_def
  set h : 𝔭.adicCompletion K := y - 1 with hh_def
  have hwy : Valued.v y = 1 := by rw [hy_def, map_pow, hwv, one_pow]
  have hwh_le : Valued.v h ≤ 1 := by
    calc Valued.v h ≤ max (Valued.v y) (Valued.v (1 : 𝔭.adicCompletion K)) :=
          Valuation.map_sub _ _ _
    _ ≤ 1 := by rw [hwy, map_one]; exact max_le le_rfl le_rfl

  have hyp_eq : y ^ p = (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1)) := by
    rw [hy_def, ← pow_mul, mul_comm, pow_mul, hv', ← map_pow]
  set S : 𝔭.adicCompletion K :=
    ∑ k ∈ Ioo 0 p, (1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
      * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K) with hS_def
  have hident : y ^ p = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
    have hyh : (1 : 𝔭.adicCompletion K) + h = y := by rw [hh_def]; ring
    calc y ^ p = ((1 : 𝔭.adicCompletion K) + h) ^ p := by rw [hyh]
    _ = 1 ^ p + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by
          rw [add_pow_prime_eq hp]
    _ = 1 + h ^ p + (p : 𝔭.adicCompletion K) * 1 * h * S := by rw [one_pow]
  have hzL : (algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)
      = h ^ p + (p : 𝔭.adicCompletion K) * h * S := by
    rw [map_sub, map_one, ← hyp_eq, hident]; ring

  have hwnat : ∀ n : ℕ, Valued.v ((n : 𝔭.adicCompletion K)) ≤ 1 := by
    intro n
    have hcast : ((n : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) (n : R) := by
      rw [map_natCast]
    rw [hcast, hwR]; exact intValuation_le_one 𝔭 _
  have hwS : Valued.v S ≤ 1 := by
    rw [hS_def]
    refine Valuation.map_sum_le _ ?_
    intro k _
    calc Valued.v ((1 : 𝔭.adicCompletion K) ^ (k - 1) * h ^ (p - k - 1)
          * ((p.choose k / p : ℕ) : 𝔭.adicCompletion K))
        = (Valued.v (1 : 𝔭.adicCompletion K)) ^ (k - 1) * (Valued.v h) ^ (p - k - 1)
          * Valued.v (((p.choose k / p : ℕ) : 𝔭.adicCompletion K)) := by
          rw [map_mul, map_mul, map_pow, map_pow]
    _ ≤ 1 := by
          rw [map_one, one_pow, one_mul]
          exact mul_le_one' (pow_le_one' hwh_le _) (hwnat _)
  have hwp2 : Valued.v ((p : 𝔭.adicCompletion K)) ≤ exp (-2 : ℤ) := by
    have hcast : ((p : 𝔭.adicCompletion K)) = (algebraMap R (𝔭.adicCompletion K)) ((p : ℕ) : R) := by
      rw [map_natCast]
    rw [hcast, hwR]
    have h2 := (intValuation_le_pow_iff_mem 𝔭 ((p : ℕ) : R) 2).mpr hp2
    simpa using h2
  have hwz_lt : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) < 1 := by
    rw [hwR]; exact (intValuation_lt_one_iff_mem 𝔭 _).mpr hz1
  have hwp_lt : Valued.v ((p : 𝔭.adicCompletion K)) < 1 :=
    lt_of_le_of_lt hwp2 (by rw [← exp_zero, exp_lt_exp]; omega)

  have hwh_lt : Valued.v h < 1 := by
    rcases lt_or_eq_of_le hwh_le with hlt | heq
    · exact hlt
    · exfalso
      have h1 : Valued.v (h ^ p) = 1 := by rw [map_pow, heq, one_pow]
      have h2 : Valued.v ((p : 𝔭.adicCompletion K) * h * S) < 1 := by
        calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
            = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
              rw [map_mul, map_mul]
        _ ≤ Valued.v ((p : 𝔭.adicCompletion K)) * 1 * 1 :=
              mul_le_mul' (mul_le_mul' le_rfl heq.le) hwS
        _ = Valued.v ((p : 𝔭.adicCompletion K)) := by rw [mul_one, mul_one]
        _ < 1 := hwp_lt
      have h3 : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1)) = 1 := by
        rw [hzL, Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1]
      exact absurd h3 (ne_of_lt hwz_lt)
  have hwh_le' : Valued.v h ≤ exp (-1 : ℤ) := zm0_le_exp_neg_one_of_lt_one hwh_lt

  have hfinal : Valued.v ((algebraMap R (𝔭.adicCompletion K)) ((u : R) ^ (p - 1) - 1))
      ≤ exp (-3 : ℤ) := by
    rw [hzL]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [map_pow]
      have hb1 : (Valued.v h) ^ p ≤ (exp (-1 : ℤ)) ^ p := pow_le_pow_left' hwh_le' p
      have hb2 : (exp (-1 : ℤ)) ^ p = exp (-(p : ℤ)) := by
        rw [← exp_nsmul]
        congr 1
        rw [nsmul_eq_mul]
        ring
      rw [hb2] at hb1
      exact le_trans hb1 (by rw [exp_le_exp]; omega)
    · calc Valued.v ((p : 𝔭.adicCompletion K) * h * S)
          = Valued.v ((p : 𝔭.adicCompletion K)) * Valued.v h * Valued.v S := by
            rw [map_mul, map_mul]
      _ ≤ exp (-2 : ℤ) * exp (-1 : ℤ) * 1 :=
            mul_le_mul' (mul_le_mul' hwp2 hwh_le') hwS
      _ = exp (-3 : ℤ) := by rw [mul_one, ← exp_add]; norm_num

  have hle : 𝔭.intValuation ((u : R) ^ (p - 1) - 1) ≤ exp (-(3 : ℕ) : ℤ) := by
    rw [← hwR]
    simpa using hfinal
  exact (intValuation_le_pow_iff_mem 𝔭 _ 3).mp hle

end ExtCitation.Cyclotomic.B2Con

set_option autoImplicit false

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "unitsEnd unitsEnd_proj unitsGalAction unitsOmegaEigenspace omegaIdempotent finrank_unitsOmegaEigenspace_two"
namespace B2Con
p2m_open "ExtCitation.Cyclotomic ExtCitation"

variable {Q : Type*} [CommRing Q]

private def tlog (h : Q) (z : Q) : Q := (z - 1) - h * (z - 1) ^ 2

private theorem tlog_one (h : Q) : tlog h 1 = 0 := by simp [tlog]

private theorem tlog_mul {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) {z w : Q} (hz : z - 1 ∈ J) (hw : w - 1 ∈ J) :
    tlog h (z * w) = tlog h z + tlog h w := by
  obtain ⟨a, rfl⟩ : ∃ a, z = 1 + a := ⟨z - 1, by ring⟩
  obtain ⟨b, rfl⟩ : ∃ b, w = 1 + b := ⟨w - 1, by ring⟩
  simp only [add_sub_cancel_left] at hz hw
  have h1 : a * a * b = 0 := hJ a hz a hz b hw
  have h3 : a * b * b = 0 := hJ a hz b hw b hw
  have key : tlog h ((1 + a) * (1 + b)) - (tlog h (1 + a) + tlog h (1 + b)) =
      (1 - 2 * h) * (a * b) - h * (2 * (a * a * b) + 2 * (a * b * b) + (a * a * b) * b) := by
    unfold tlog; ring
  rw [h1, h3, h2] at key
  rw [← sub_eq_zero, key]
  ring

private theorem map_tlog {Q' : Type*} [CommRing Q'] (f : Q →+* Q') (h : Q) (z : Q) :
    f (tlog h z) = tlog (f h) (f z) := by
  simp [tlog, map_sub, map_mul, map_pow]

private theorem tlog_mem {J : Ideal Q} (h : Q) {z : Q} (hz : z - 1 ∈ J) : tlog h z ∈ J := by
  unfold tlog
  exact J.sub_mem hz (J.mul_mem_left _ (by rw [pow_two]; exact J.mul_mem_left _ hz))

section Hom

variable {G : Type*} [Group G]

private def tlogHom {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) : Additive G →+ Q where
  toFun x := tlog h (f x.toMul)
  map_zero' := by simp [tlog_one]
  map_add' x y := by
    simp only [toMul_add, map_mul]
    exact tlog_mul hJ h2 (hf _) (hf _)

@[scoped simp] private theorem tlogHom_apply {J : Ideal Q} (hJ : ∀ a ∈ J, ∀ b ∈ J, ∀ c ∈ J, a * b * c = 0)
    {h : Q} (h2 : 2 * h = 1) (f : G →* Q) (hf : ∀ g, f g - 1 ∈ J) (g : G) :
    tlogHom hJ h2 f hf (Additive.ofMul g) = tlog h (f g) := rfl

end Hom

section Cyclo

p2m_open "NumberField IsCyclotomicExtension Polynomial Ideal NumberField.Ideal"

variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {p} ℚ K]

private noncomputable def zeta0 : 𝓞 K := (zeta_spec p ℚ K).toInteger

private noncomputable def lam : 𝓞 K := zeta0 p K - 1

private noncomputable def PP : Ideal (𝓞 K) := Ideal.span {lam p K}

private theorem lam_prime : Prime (lam p K) := (zeta_spec p ℚ K).zeta_sub_one_prime'

private theorem lam_ne_zero : lam p K ≠ 0 := (lam_prime p K).ne_zero

private theorem lam_not_isUnit : ¬ IsUnit (lam p K) := (lam_prime p K).not_unit

private scoped instance PP_isPrime : (PP p K).IsPrime :=
  IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' p (zeta_spec p ℚ K)

private theorem PP_ne_bot : PP p K ≠ ⊥ := by
  rw [PP, Ne, Ideal.span_singleton_eq_bot]
  exact lam_ne_zero p K

private noncomputable def v0 : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨PP p K, inferInstance, PP_ne_bot p K⟩

@[scoped simp] private theorem v0_asIdeal : (v0 p K).asIdeal = PP p K := rfl

private theorem natCast_mem_PP_pow : (p : 𝓞 K) ∈ PP p K ^ (p - 1) := by
  have hK' : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hK
  have hζ' : IsPrimitiveRoot (zeta p ℚ K) (p ^ (0 + 1)) := by simpa using zeta_spec p ℚ K
  have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ'
  have hfin : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank p K, Nat.totient_prime hp.out]
  have hmem : (p : 𝓞 K) ∈ Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) := by
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  rw [h, hfin] at hmem
  exact hmem

private theorem natCast_mem_PP : (p : 𝓞 K) ∈ PP p K :=
  Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hp.out.one_lt) (natCast_mem_PP_pow p K)

private theorem natCast_mem_PP_pow_three (hp5 : 5 ≤ p) : (p : 𝓞 K) ∈ PP p K ^ 3 :=
  Ideal.pow_le_pow_right (by omega) (natCast_mem_PP_pow p K)

private theorem natCast_mem_PP_pow_two (hp5 : 5 ≤ p) : (p : 𝓞 K) ∈ PP p K ^ 2 :=
  Ideal.pow_le_pow_right (by omega) (natCast_mem_PP_pow p K)

private theorem card_quot_PP : Nat.card (𝓞 K ⧸ PP p K) = p := by
  have hK' : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hK
  have hζ' : IsPrimitiveRoot (zeta p ℚ K) (p ^ (0 + 1)) := by simpa using zeta_spec p ℚ K
  have h := IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 hζ'
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  exact h

private scoped instance finite_quot_PP : Finite (𝓞 K ⧸ PP p K) :=
  (zeta_spec p ℚ K).finite_quotient_span_sub_one'

private theorem charP_quot_PP : CharP (𝓞 K ⧸ PP p K) p :=
  have : Nontrivial (𝓞 K ⧸ PP p K) :=
    Ideal.Quotient.nontrivial_iff.mpr (PP_isPrime p K).ne_top
  (CharP.charP_iff_prime_eq_zero hp.out).2
    ((Ideal.Quotient.eq_zero_iff_mem).2 (natCast_mem_PP p K))

private theorem exists_nat_sub_mem_PP (x : 𝓞 K) : ∃ n : ℕ, x - n ∈ PP p K := by
  haveI := charP_quot_PP p K
  have : Nontrivial (𝓞 K ⧸ PP p K) :=
    Ideal.Quotient.nontrivial_iff.mpr (PP_isPrime p K).ne_top
  let f : ZMod p →+* 𝓞 K ⧸ PP p K := ZMod.castHom (dvd_refl p) _
  have hinj : Function.Injective f := f.injective
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by
    rw [card_quot_PP p K, Nat.card_eq_fintype_card, ZMod.card])
  obtain ⟨c, hc⟩ := hbij.2 (Ideal.Quotient.mk (PP p K) x)
  refine ⟨c.val, ?_⟩
  rw [← Ideal.Quotient.eq, ← hc, map_natCast]
  show ZMod.castHom _ _ c = _
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem units_pow_sub_one_mem_PP (u : (𝓞 K)ˣ) : (u : 𝓞 K) ^ (p - 1) - 1 ∈ PP p K := by
  haveI := charP_quot_PP p K
  have : Nontrivial (𝓞 K ⧸ PP p K) :=
    Ideal.Quotient.nontrivial_iff.mpr (PP_isPrime p K).ne_top
  obtain ⟨n, hn⟩ := exists_nat_sub_mem_PP p K (u : 𝓞 K)
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hn
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_pow, sub_eq_zero, hn, map_natCast]

  let φ := ZMod.castHom (dvd_refl p) (𝓞 K ⧸ PP p K)
  have hφn : φ (n : ZMod p) = (n : 𝓞 K ⧸ PP p K) := map_natCast φ n
  have hu : IsUnit (n : 𝓞 K ⧸ PP p K) := by
    have := u.isUnit.map (Ideal.Quotient.mk (PP p K))
    rwa [hn, map_natCast] at this
  have hnz : (n : ZMod p) ≠ 0 := by
    intro h0
    rw [← hφn, h0, map_zero] at hu
    exact not_isUnit_zero hu
  have key : (n : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hnz
  have := congrArg φ key
  rwa [map_pow, map_one, hφn] at this

private noncomputable def tQ : 𝓞 K ⧸ PP p K ^ 3 := Ideal.Quotient.mk _ (lam p K)

private theorem tQ_pow_three : tQ p K ^ 3 = 0 := by
  rw [tQ, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, PP, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

private theorem tQ_sq_ne_zero : tQ p K ^ 2 ≠ 0 := by
  rw [tQ, ← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, PP, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, pow_dvd_pow_iff (lam_ne_zero p K) (lam_not_isUnit p K)]
  omega

private scoped instance nontrivial_Q : Nontrivial (𝓞 K ⧸ PP p K ^ 3) :=
  Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    have := Ideal.pow_le_self (I := PP p K) (n := 3) (by norm_num)
    rw [h, top_le_iff] at this
    exact (PP_isPrime p K).ne_top this)

private theorem natCast_Q_eq_zero (hp5 : 5 ≤ p) : (p : 𝓞 K ⧸ PP p K ^ 3) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (PP p K ^ 3)), Ideal.Quotient.eq_zero_iff_mem]
  exact natCast_mem_PP_pow_three p K hp5

private theorem charP_Q (hp5 : 5 ≤ p) : CharP (𝓞 K ⧸ PP p K ^ 3) p :=
  (CharP.charP_iff_prime_eq_zero hp.out).2 (natCast_Q_eq_zero p K hp5)

private noncomputable def iota (hp5 : 5 ≤ p) : ZMod p →+* 𝓞 K ⧸ PP p K ^ 3 :=
  haveI := charP_Q p K hp5
  ZMod.castHom (dvd_refl p) _

private theorem iota_apply (hp5 : 5 ≤ p) (c : ZMod p) : iota p K hp5 c = (c.val : 𝓞 K ⧸ PP p K ^ 3) := by
  haveI := charP_Q p K hp5
  rw [iota, ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem iota_natCast (hp5 : 5 ≤ p) (n : ℕ) : iota p K hp5 n = n := map_natCast _ n

private noncomputable def hh (hp5 : 5 ≤ p) : 𝓞 K ⧸ PP p K ^ 3 := iota p K hp5 2⁻¹

private theorem two_ne_zero_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
  have := Nat.le_of_dvd (by norm_num) this
  omega

private theorem two_mul_hh (hp5 : 5 ≤ p) : 2 * hh p K hp5 = 1 := by
  rw [hh, ← map_ofNat (iota p K hp5) 2, ← map_mul, mul_inv_cancel₀ (two_ne_zero_zmod p hp5),
    map_one]

private theorem J_cube (a : 𝓞 K ⧸ PP p K ^ 3) (ha : a ∈ Ideal.span {tQ p K})
    (b : 𝓞 K ⧸ PP p K ^ 3) (hb : b ∈ Ideal.span {tQ p K})
    (c : 𝓞 K ⧸ PP p K ^ 3) (hc : c ∈ Ideal.span {tQ p K}) : a * b * c = 0 := by
  rw [Ideal.mem_span_singleton] at ha hb hc
  obtain ⟨a', rfl⟩ := ha; obtain ⟨b', rfl⟩ := hb; obtain ⟨c', rfl⟩ := hc
  have : tQ p K * a' * (tQ p K * b') * (tQ p K * c') = tQ p K ^ 3 * (a' * b' * c') := by ring
  rw [this, tQ_pow_three, zero_mul]

private noncomputable def f0 : (𝓞 K)ˣ →* 𝓞 K ⧸ PP p K ^ 3 :=
  (powMonoidHom (p - 1)).comp ((Ideal.Quotient.mk (PP p K ^ 3)).toMonoidHom.comp (Units.coeHom _))

@[scoped simp] private theorem f0_apply (u : (𝓞 K)ˣ) :
    f0 p K u = (Ideal.Quotient.mk (PP p K ^ 3) (u : 𝓞 K)) ^ (p - 1) := rfl

private theorem mk_mem_span_tQ {x : 𝓞 K} (hx : x ∈ PP p K) :
    Ideal.Quotient.mk (PP p K ^ 3) x ∈ Ideal.span {tQ p K} := by
  rw [PP, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, Ideal.mem_span_singleton]
  exact ⟨_, rfl⟩

private theorem f0_sub_one_mem (u : (𝓞 K)ˣ) : f0 p K u - 1 ∈ Ideal.span {tQ p K} := by
  have h := mk_mem_span_tQ p K (units_pow_sub_one_mem_PP p K u)
  simpa using h

private noncomputable def LamT (hp5 : 5 ≤ p) : Additive (𝓞 K)ˣ →+ 𝓞 K ⧸ PP p K ^ 3 :=
  tlogHom (J_cube p K) (two_mul_hh p K hp5) (f0 p K) (f0_sub_one_mem p K)

private theorem LamT_apply (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ) :
    LamT p K hp5 (Additive.ofMul u) =
      tlog (hh p K hp5) ((Ideal.Quotient.mk (PP p K ^ 3) (u : 𝓞 K)) ^ (p - 1)) := rfl

private theorem LamT_nsmul_p (hp5 : 5 ≤ p) (x : Additive (𝓞 K)ˣ) : LamT p K hp5 (p • x) = 0 := by
  rw [map_nsmul, nsmul_eq_mul, natCast_Q_eq_zero p K hp5, zero_mul]

private theorem LamT_eq_zero_of (hp5 : 5 ≤ p) (u : (𝓞 K)ˣ)
    (hu : (u : 𝓞 K) ^ (p - 1) - 1 ∈ PP p K ^ 3) : LamT p K hp5 (Additive.ofMul u) = 0 := by
  rw [LamT_apply]
  have : (Ideal.Quotient.mk (PP p K ^ 3) (u : 𝓞 K)) ^ (p - 1) = 1 := by
    rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk (PP p K ^ 3)), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hu
  rw [this, tlog_one]

private theorem two_coprime (hp5 : 5 ≤ p) : Nat.Coprime 2 p :=
  (Nat.coprime_primes Nat.prime_two hp.out).2 (by omega)

private theorem isUnit_one_add_zeta0 (hp5 : 5 ≤ p) : IsUnit (1 + zeta0 p K) := by
  have hζ := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  have := hζ.geom_sum_isUnit hp.out.two_le (two_coprime p hp5)
  simpa [Finset.sum_range_succ, zeta0] using this

private noncomputable def c2 (hp5 : 5 ≤ p) : (𝓞 K)ˣ := (isUnit_one_add_zeta0 p K hp5).unit

@[scoped simp] private theorem c2_val (hp5 : 5 ≤ p) : (c2 p K hp5 : 𝓞 K) = 1 + zeta0 p K :=
  (isUnit_one_add_zeta0 p K hp5).unit_spec

private theorem mk_zeta0 : Ideal.Quotient.mk (PP p K ^ 3) (zeta0 p K) = 1 + tQ p K := by
  rw [tQ, ← map_one (Ideal.Quotient.mk (PP p K ^ 3)), ← map_add, lam, add_sub_cancel]

private theorem exists_map_zeta0_eq_pow (σ : 𝓞 K ≃+* 𝓞 K) : ∃ a : ℕ, σ (zeta0 p K) = zeta0 p K ^ a := by
  have hζ := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one (ξ := σ (zeta0 p K))
    (by rw [← map_pow, zeta0, hζ.pow_eq_one, map_one])
  exact ⟨a, ha.symm⟩

private theorem two_mul_choose_two_add (a : ℕ) : 2 * a.choose 2 + a = a ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    zify at ih ⊢
    push_cast at ih ⊢
    linear_combination ih

section QRing

variable {Q : Type*} [CommRing Q]

private theorem one_add_pow_trunc {t : Q} (ht : t ^ 3 = 0) (a : ℕ) :
    (1 + t) ^ a = 1 + (a : Q) * t + (a.choose 2 : Q) * t ^ 2 := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linear_combination (n.choose 2 : Q) * ht

private theorem cast_choose_two (a : ℕ) : (2 : Q) * (a.choose 2 : Q) = (a : Q) ^ 2 - a := by
  have h := congrArg (Nat.cast : ℕ → Q) (two_mul_choose_two_add a)
  push_cast at h
  linear_combination h

private theorem two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : (2 + s) ^ (p - 1) = 1 - h * s + h ^ 2 * s ^ 2 := by
  have hsp : s ^ p = 0 := pow_eq_zero_of_le hp3 hs
  have h2p : (2 : Q) ^ p = 2 := by
    have e : (ZMod.castHom (dvd_refl p) Q) 2 = (2 : Q) := map_ofNat _ 2
    rw [← e, ← map_pow, ZMod.pow_card]
  have hp1 : (2 + s) ^ p = 2 := by rw [add_pow_char, hsp, h2p, add_zero]
  have hA : (1 - h * s + h ^ 2 * s ^ 2) * (2 + s) = 2 := by
    linear_combination (-s + h * s ^ 2) * h2 + h ^ 2 * hs
  have hsucc : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  calc (2 + s) ^ (p - 1)
      = (2 + s) ^ (p - 1) * (h * ((1 - h * s + h ^ 2 * s ^ 2) * (2 + s))) := by
          rw [hA, mul_comm h 2, h2, mul_one]
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * ((2 + s) ^ (p - 1) * (2 + s)) := by ring
    _ = h * (1 - h * s + h ^ 2 * s ^ 2) * 2 := by rw [← pow_succ, hsucc, hp1]
    _ = 1 - h * s + h ^ 2 * s ^ 2 := by linear_combination (1 - h * s + h ^ 2 * s ^ 2) * h2

private theorem tlog_two_add_pow_sub_one [CharP Q p] (hp3 : 3 ≤ p) {h s : Q} (h2 : 2 * h = 1)
    (hs : s ^ 3 = 0) : tlog h ((2 + s) ^ (p - 1)) = -(h * s) + (h ^ 2 - h ^ 3) * s ^ 2 := by
  rw [two_add_pow_sub_one p hp3 h2 hs, tlog]
  linear_combination (2 * h ^ 4 - h ^ 5 * s) * hs

private theorem tlog_conj_eval [CharP Q p] (hp3 : 3 ≤ p) {h t : Q} (h2 : 2 * h = 1)
    (ht : t ^ 3 = 0) (a : ℕ) :
    tlog h ((1 + (1 + t) ^ a) ^ (p - 1)) =
      -(h * a) * t + (h ^ 2 * a - h ^ 3 * (a : Q) ^ 2) * t ^ 2 := by
  set T : Q := (a.choose 2 : Q) with hTdef
  have hT : 2 * T = (a : Q) ^ 2 - a := cast_choose_two a
  have hs : (1 + t) ^ a = 1 + (a : Q) * t + T * t ^ 2 := one_add_pow_trunc ht a
  have hs3 : ((a : Q) * t + T * t ^ 2) ^ 3 = 0 := by
    have : ((a : Q) * t + T * t ^ 2) ^ 3 = t ^ 3 * ((a : Q) + T * t) ^ 3 := by ring
    rw [this, ht, zero_mul]
  have : (1 + (1 + t) ^ a) = 2 + ((a : Q) * t + T * t ^ 2) := by rw [hs]; ring
  rw [this, tlog_two_add_pow_sub_one p hp3 h2 hs3]
  linear_combination (h * T * t ^ 2) * h2 + (-(h ^ 2 * t ^ 2)) * hT +
    ((h ^ 2 - h ^ 3) * (2 * (a : Q) * T + T ^ 2 * t)) * ht

end QRing

private theorem LamT_conj (hp5 : 5 ≤ p) (σ : 𝓞 K ≃+* 𝓞 K) (a : ℕ) (hσ : σ (zeta0 p K) = zeta0 p K ^ a) :
    LamT p K hp5 (Additive.ofMul (Units.mapEquiv σ.toMulEquiv (c2 p K hp5))) =
      -(hh p K hp5 * a) * tQ p K +
        (hh p K hp5 ^ 2 * a - hh p K hp5 ^ 3 * (a : 𝓞 K ⧸ PP p K ^ 3) ^ 2) * tQ p K ^ 2 := by
  haveI := charP_Q p K hp5
  rw [LamT_apply]
  have hcoe : ((Units.mapEquiv σ.toMulEquiv (c2 p K hp5) : (𝓞 K)ˣ) : 𝓞 K) = σ (1 + zeta0 p K) := by
    simp [Units.coe_mapEquiv]
  rw [hcoe, map_add, map_one, hσ, map_add, map_one, map_pow, mk_zeta0]
  exact tlog_conj_eval p (by omega) (two_mul_hh p K hp5) (tQ_pow_three p K) a

private theorem galRestrict_autEquivPow_symm_zeta0 (hirr : Irreducible (cyclotomic p ℚ))
    (d : (ZMod p)ˣ) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    galRestrict ℤ ℚ K (𝓞 K) ((autEquivPow K hirr).symm d) (zeta0 p K) =
      zeta0 p K ^ (d : ZMod p).val := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  set σ := (autEquivPow K hirr).symm d with hσ
  apply RingOfIntegers.coe_injective
  have h1 : ((galRestrict ℤ ℚ K (𝓞 K) σ (zeta0 p K) : 𝓞 K) : K) = σ (zeta0 p K : K) :=
    algebraMap_galRestrict_apply ℤ σ (zeta0 p K)
  have h2 : (zeta_spec p ℚ K).autToPow ℚ σ = d := by
    have := (autEquivPow K hirr).apply_symm_apply d
    rwa [autEquivPow_apply] at this
  have h3 := (zeta_spec p ℚ K).autToPow_spec ℚ σ
  rw [h2] at h3

  refine (algebraMap_galRestrict_apply ℤ σ (zeta0 p K)).trans ?_
  have hz : algebraMap (𝓞 K) K (zeta0 p K) = zeta p ℚ K := rfl
  rw [map_pow, hz]
  exact h3.symm

private theorem zmod_units_ne_zero (d : (ZMod p)ˣ) : (d : ZMod p) ≠ 0 := d.ne_zero

private theorem sum_units_val (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p) = 0 := by
  have h := FiniteField.sum_pow_units (K := ZMod p) 1
  simp only [pow_one, ZMod.card] at h
  rw [h, if_neg]
  intro hdvd
  have := Nat.le_of_dvd Nat.one_pos hdvd
  omega

private theorem sum_units_inv (hp5 : 5 ≤ p) : ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = 0 := by
  calc ∑ d : (ZMod p)ˣ, (d : ZMod p)⁻¹ = ∑ d : (ZMod p)ˣ, ((d⁻¹ : (ZMod p)ˣ) : ZMod p) :=
        Finset.sum_congr rfl fun d _ => (Units.val_inv_eq_inv_val d).symm
    _ = ∑ d : (ZMod p)ˣ, (d : ZMod p) :=
        Fintype.sum_equiv (Equiv.inv (ZMod p)ˣ) _ _ (fun _ => rfl)
    _ = 0 := sum_units_val p hp5

private theorem sum_units_one : ∑ _d : (ZMod p)ˣ, (1 : ZMod p) = -1 := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, mul_one,
    Nat.cast_sub hp.out.one_le, Nat.cast_one, ZMod.natCast_self, zero_sub]

private theorem card_units_inv : ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ = -1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units p, Nat.cast_sub hp.out.one_le, Nat.cast_one,
    ZMod.natCast_self, zero_sub, inv_neg, inv_one]

private theorem e2_sum (hp5 : 5 ≤ p) :
    iota p K hp5 ((Nat.card (ZMod p)ˣ : ZMod p))⁻¹ *
      ∑ d : (ZMod p)ˣ, iota p K hp5 (((d : ZMod p) ^ 2)⁻¹) *
        (-(hh p K hp5 * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3)) * tQ p K +
          (hh p K hp5 ^ 2 * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3) -
            hh p K hp5 ^ 3 * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3) ^ 2) * tQ p K ^ 2) =
      -(hh p K hp5 ^ 3 * tQ p K ^ 2) := by
  simp only [hh]
  set ι := iota p K hp5 with hι
  set t := tQ p K
  have hval : ∀ d : (ZMod p)ˣ, ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3) = ι d := fun d =>
    (iota_apply p K hp5 d).symm
  have hsummand : ∀ d : (ZMod p)ˣ,
      ι (((d : ZMod p) ^ 2)⁻¹) *
        (-(ι 2⁻¹ * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3)) * t +
          ((ι 2⁻¹) ^ 2 * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3) -
            (ι 2⁻¹) ^ 3 * ((d : ZMod p).val : 𝓞 K ⧸ PP p K ^ 3) ^ 2) * t ^ 2) =
      ι (-(2⁻¹ * (d : ZMod p)⁻¹)) * t + ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) * t ^ 2 := by
    intro d
    have hd : (d : ZMod p) ≠ 0 := d.ne_zero
    have e1 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) = (d : ZMod p)⁻¹ := by
      field_simp
    have e2 : ((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hd)
    rw [hval d]
    have : ι (-(2⁻¹ * (d : ZMod p)⁻¹)) = -(ι (((d : ZMod p) ^ 2)⁻¹) * (ι 2⁻¹ * ι d)) := by
      rw [← e1]; simp only [map_neg, map_mul]; ring
    rw [this]
    have : ι ((2⁻¹) ^ 2 * (d : ZMod p)⁻¹ - (2⁻¹) ^ 3) =
        ι (((d : ZMod p) ^ 2)⁻¹) * ((ι 2⁻¹) ^ 2 * ι d - (ι 2⁻¹) ^ 3 * (ι d) ^ 2) := by
      rw [← e1]
      conv_lhs => rw [show ((2 : ZMod p)⁻¹) ^ 3 = (2⁻¹) ^ 3 * (((d : ZMod p) ^ 2)⁻¹ * (d : ZMod p) ^ 2)
        by rw [e2, mul_one]]
      simp only [map_sub, map_mul, map_pow]; ring
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun d _ => hsummand d), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, ← map_sum, ← map_sum]
  have s1 : ∑ d : (ZMod p)ˣ, -(2⁻¹ * (d : ZMod p)⁻¹) = 0 := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum, sum_units_inv p hp5, mul_zero, neg_zero]
  have s2 : ∑ d : (ZMod p)ˣ, ((2 : ZMod p)⁻¹ ^ 2 * (d : ZMod p)⁻¹ - 2⁻¹ ^ 3) = 2⁻¹ ^ 3 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_units_inv p hp5, mul_zero, Finset.sum_const,
      Finset.card_univ, ZMod.card_units p, nsmul_eq_mul, Nat.cast_sub hp.out.one_le, Nat.cast_one,
      ZMod.natCast_self]
    ring
  rw [s1, s2, card_units_inv p, map_zero, zero_mul, zero_add, map_neg, map_one, map_pow]
  ring

private theorem hh_cube_mul_tQ_sq_ne_zero (hp5 : 5 ≤ p) : hh p K hp5 ^ 3 * tQ p K ^ 2 ≠ 0 := by
  intro h0
  apply tQ_sq_ne_zero p K
  calc tQ p K ^ 2 = (2 * hh p K hp5) ^ 3 * tQ p K ^ 2 := by rw [two_mul_hh, one_pow, one_mul]
    _ = 8 * (hh p K hp5 ^ 3 * tQ p K ^ 2) := by ring
    _ = 0 := by rw [h0, mul_zero]

end Cyclo

end ExtCitation.Cyclotomic.B2Con
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation"

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "unitsEnd unitsEnd_proj unitsGalAction unitsOmegaEigenspace omegaIdempotent finrank_unitsOmegaEigenspace_two"
namespace B2Con
p2m_open "ExtCitation.Cyclotomic ExtCitation"

open NumberField IsCyclotomicExtension JacobiSumStickelberger Stickelberger

section Heavy

variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def Lam (hp5 : 5 ≤ p) :
    ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) →+
      𝓞 (CyclotomicField p ℚ) ⧸ PP p (CyclotomicField p ℚ) ^ 3 :=
  QuotientAddGroup.lift (nsmulRange p (Additive (𝓞 (CyclotomicField p ℚ))ˣ))
    (LamT p (CyclotomicField p ℚ) hp5) (by
      rintro _ ⟨x, rfl⟩
      exact LamT_nsmul_p p _ hp5 x)

private theorem Lam_proj (hp5 : 5 ≤ p) (x : Additive (𝓞 (CyclotomicField p ℚ))ˣ) :
    Lam p hp5 (ModP.proj p _ x) = LamT p (CyclotomicField p ℚ) hp5 x := rfl

private theorem Lam_proj_eq_zero_of (hp5 : 5 ≤ p) (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hu : (u : 𝓞 (CyclotomicField p ℚ)) ^ (p - 1) - 1 ∈ PP p (CyclotomicField p ℚ) ^ 3) :
    Lam p hp5 (ModP.proj p _ (Additive.ofMul u)) = 0 := by
  rw [Lam_proj]
  exact LamT_eq_zero_of p _ hp5 u hu

private theorem Lam_smul (hp5 : 5 ≤ p) (c : ZMod p) (y : ModP p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)) :
    Lam p hp5 (c • y) = iota p (CyclotomicField p ℚ) hp5 c * Lam p hp5 y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul, iota_apply]

private theorem Lam_unitsGalAction_proj (hp5 : 5 ≤ p) (d : (ZMod p)ˣ) (u : (𝓞 (CyclotomicField p ℚ))ˣ) :
    Lam p hp5 (unitsGalAction p d (ModP.proj p _ (Additive.ofMul u))) =
      LamT p (CyclotomicField p ℚ) hp5 (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u)) := by
  show Lam p hp5 (unitsEnd p _ (clRingAction p (CyclotomicField p ℚ) d)
    (ModP.proj p _ (Additive.ofMul u))) = _
  rw [unitsEnd_proj]
  rfl

private theorem clRingAction_zeta0 (d : (ZMod p)ˣ) :
    clRingAction p (CyclotomicField p ℚ) d (zeta0 p (CyclotomicField p ℚ)) =
      zeta0 p (CyclotomicField p ℚ) ^ (d : ZMod p).val := by
  have h := galRestrict_autEquivPow_symm_zeta0 p (CyclotomicField p ℚ)
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne p))) d
  exact h

private theorem Lam_omegaIdempotent_two_c2 (hp5 : 5 ≤ p) :
    Lam p hp5 (omegaIdempotent p (unitsGalAction p) 2
      (ModP.proj p _ (Additive.ofMul (c2 p (CyclotomicField p ℚ) hp5)))) =
      -(hh p (CyclotomicField p ℚ) hp5 ^ 3 * tQ p (CyclotomicField p ℚ) ^ 2) := by
  rw [omegaIdempotent, LinearMap.smul_apply, LinearMap.sum_apply, Lam_smul, map_sum]
  simp only [LinearMap.smul_apply, Lam_smul, Lam_unitsGalAction_proj]
  have hconj : ∀ d : (ZMod p)ˣ,
      LamT p (CyclotomicField p ℚ) hp5 (Additive.ofMul
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv
          (c2 p (CyclotomicField p ℚ) hp5))) = _ :=
    fun d => LamT_conj p (CyclotomicField p ℚ) hp5 _ _ (clRingAction_zeta0 p d)
  simp only [hconj]
  exact e2_sum p (CyclotomicField p ℚ) hp5

private theorem Lam_omegaIdempotent_two_c2_ne_zero (hp5 : 5 ≤ p) :
    Lam p hp5 (omegaIdempotent p (unitsGalAction p) 2
      (ModP.proj p _ (Additive.ofMul (c2 p (CyclotomicField p ℚ) hp5)))) ≠ 0 := by
  rw [Lam_omegaIdempotent_two_c2, neg_ne_zero]
  exact hh_cube_mul_tQ_sq_ne_zero p (CyclotomicField p ℚ) hp5

private theorem eq_zero_of_iota_mul_eq_zero (hp5 : 5 ≤ p) (a : ZMod p)
    {x : 𝓞 (CyclotomicField p ℚ) ⧸ PP p (CyclotomicField p ℚ) ^ 3} (hx : x ≠ 0)
    (h : iota p (CyclotomicField p ℚ) hp5 a * x = 0) : a = 0 := by
  by_contra ha
  apply hx
  have : iota p (CyclotomicField p ℚ) hp5 a⁻¹ * (iota p (CyclotomicField p ℚ) hp5 a * x) = x := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rw [← this, h, mul_zero]

end Heavy
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"

end ExtCitation.Cyclotomic.B2Con
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"

namespace ExtCitation
namespace Cyclotomic
p2m_export "ExtCitation.Cyclotomic" "unitsEnd unitsEnd_proj unitsGalAction unitsOmegaEigenspace omegaIdempotent finrank_unitsOmegaEigenspace_two"
namespace B2Con
p2m_open "ExtCitation.Cyclotomic ExtCitation"

open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger

section Generic
variable {p : ℕ} [Fact p.Prime]

private theorem isOmegaEigenvector_omegaIdempotent {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    (ρ : (ZMod p)ˣ →* Module.End (ZMod p) M) (i : ℕ) (x : M) :
    IsOmegaEigenvector ρ i (omegaIdempotent p ρ i x) := by
  intro d₀
  simp only [omegaIdempotent, LinearMap.smul_apply, Finset.sum_apply, LinearMap.coe_sum]
  rw [map_smul, map_sum]
  simp only [map_smul]
  rw [smul_comm ((d₀ : ZMod p) ^ i)]
  congr 1
  rw [Finset.smul_sum]
  refine Fintype.sum_bijective (fun d => d₀ * d) (Group.mulLeft_bijective d₀) _ _ ?_
  intro d
  rw [← Module.End.mul_apply, ← map_mul ρ, smul_smul]
  congr 1
  have hd : (d : ZMod p) ≠ 0 := d.ne_zero
  have hd₀ : (d₀ : ZMod p) ≠ 0 := d₀.ne_zero
  push_cast
  field_simp
  ring

private theorem exists_smul_eq_of_finrank_one {K M : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] {W : Submodule K M} (hW : Module.finrank K W = 1)
    {g : M} (hgW : g ∈ W) (hg : g ≠ 0) {x : M} (hxW : x ∈ W) :
    ∃ a : K, x = a • g := by
  have hfd : FiniteDimensional K W := .of_finrank_eq_succ hW
  have hspan : (K ∙ g) = W :=
    Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem g W).mpr hgW)
      (by rw [finrank_span_singleton hg, hW])
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hxW)
  exact ⟨a, ha.symm⟩

end Generic
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"

end ExtCitation.Cyclotomic.B2Con
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"
p2m_reactivate "P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic.B2Con"

open NumberField IsDedekindDomain JacobiSumStickelberger Stickelberger _root_.ExtCitation.Cyclotomic _root_.P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow.ExtCitation.Cyclotomic ExtCitation.Cyclotomic.B2Con in

theorem solution (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (u : (𝓞 (CyclotomicField p ℚ))ˣ)
    (heig : IsOmegaEigenvector (unitsGalAction p) 2
      (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)))
    (hloc : ∀ 𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField p ℚ)),
      (p : 𝓞 (CyclotomicField p ℚ)) ∈ 𝔭.asIdeal →
      ∃ v : (𝔭.adicCompletion (CyclotomicField p ℚ))ˣ,
        v ^ p = (Units.map (algebraMap (𝓞 (CyclotomicField p ℚ))
          (𝔭.adicCompletion (CyclotomicField p ℚ))).toMonoidHom) u) :
    ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u) = 0 := by

  have hg_eig : IsOmegaEigenvector (unitsGalAction p) 2
      (omegaIdempotent p (unitsGalAction p) 2
        (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)
          (Additive.ofMul (c2 p (CyclotomicField p ℚ) hp5)))) :=
    isOmegaEigenvector_omegaIdempotent (unitsGalAction p) 2 _
  have hLg_ne := Lam_omegaIdempotent_two_c2_ne_zero p hp5
  have hg_ne : omegaIdempotent p (unitsGalAction p) 2
      (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ)
        (Additive.ofMul (c2 p (CyclotomicField p ℚ) hp5))) ≠ 0 :=
    fun h => hLg_ne (by rw [h]; exact map_zero _)

  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_one
    (W := unitsOmegaEigenspace p 2) (finrank_unitsOmegaEigenspace_two p hp5) hg_eig hg_ne heig

  have hA : ((u : 𝓞 (CyclotomicField p ℚ))) ^ (p - 1) - 1 ∈ PP p (CyclotomicField p ℚ) ^ 3 :=
    pow_sub_one_mem_pow_three_of_local_pow (K := CyclotomicField p ℚ) (Fact.out : p.Prime) hp5
      (v0 p (CyclotomicField p ℚ)) u
      (units_pow_sub_one_mem_PP p (CyclotomicField p ℚ) u)
      (natCast_mem_PP_pow_two p (CyclotomicField p ℚ) hp5)
      (hloc (v0 p (CyclotomicField p ℚ)) (natCast_mem_PP p (CyclotomicField p ℚ)))
  have hLu : Lam p hp5 (ModP.proj p (Additive (𝓞 (CyclotomicField p ℚ))ˣ) (Additive.ofMul u)) = 0 :=
    Lam_proj_eq_zero_of p hp5 u hA

  rw [ha, Lam_smul p hp5] at hLu
  have ha0 : a = 0 := eq_zero_of_iota_mul_eq_zero p hp5 a hLg_ne hLu
  rw [ha, ha0, zero_smul]

end S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow
end P2MW
export P2MW.S_ExtCitation_Cyclotomic_unitsOmegaEigenvector_two_eq_zero_of_local_pow (solution)
