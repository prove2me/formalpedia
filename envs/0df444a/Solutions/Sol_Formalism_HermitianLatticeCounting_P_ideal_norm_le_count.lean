-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ideal_norm_le_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:40.600858+00:00
-- url     : https://prove2.me/submissions/23d8c16f-9677-4dba-b1de-854ffe50b78e

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IdealsOfNormEqIndexSet
import Theorems.Thm_Formalism_SLP_Final_omegaPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem primeSet_lemma (K : Type) [Field K] [NumberField K]
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥) :
    ∃ T : Finset (Ideal (NumberField.RingOfIntegers K)),
      (↑T : Set _) = {P | P.IsPrime ∧ I ≤ P} ∧ (∀ P ∈ T, P.IsPrime ∧ P ≠ ⊥ ∧ I ≤ P) ∧
      ∏ P ∈ T, Ideal.absNorm P ∣ Ideal.absNorm I := by
  have hn : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hfin : {P : Ideal (NumberField.RingOfIntegers K) | P.IsPrime ∧ I ≤ P}.Finite := by
    apply Set.Finite.subset ((Ideal.absNorm I).divisors.finite_toSet.biUnion
      fun d hd => Ideal.finite_setOf_absNorm_eq d)
    intro P hP
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, Nat.mem_divisors]
    exact ⟨_, ⟨Ideal.absNorm_dvd_absNorm_of_le hP.2, hn⟩, rfl⟩
  refine ⟨hfin.toFinset, by simp, ?_, ?_⟩
  · intro P hP
    rw [Set.Finite.mem_toFinset] at hP
    exact ⟨hP.1, fun h => hI (le_bot_iff.1 (h ▸ hP.2)), hP.2⟩
  · rw [← map_prod]
    apply map_dvd
    apply Finset.prod_primes_dvd
    · intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      haveI := hP.1
      exact Ideal.prime_of_isPrime (fun h => hI (le_bot_iff.1 (h ▸ hP.2))) hP.1
    · intro P hP
      rw [Set.Finite.mem_toFinset] at hP
      exact Ideal.dvd_iff_le.2 hP.2
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
private theorem normCount_lemma (K : Type) [Field K] [NumberField K] : ∀ n : ℕ, 1 ≤ n →
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard ≤
      finrank ℚ K ^ (Nat.primeFactorsList n).length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have : {I : Ideal (𝓞 K) | Ideal.absNorm I = 1} = {⊤} := by
      ext I; simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp
  have hd : 0 < finrank ℚ K := Module.finrank_pos
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  set p := n.minFac with hpdef
  set q : 𝓞 K := (p : 𝓞 K) with hqdef
  have hq0 : q ≠ 0 := by rw [hqdef]; exact_mod_cast hp.ne_zero
  have hqbot : Ideal.span {q} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hNq : Ideal.absNorm (Ideal.span {q}) = p ^ finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : q = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp [hqdef]
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  obtain ⟨T, hT, hT2, hprod⟩ := primeSet_lemma K (Ideal.span {q}) hqbot
  rw [hNq] at hprod
  have hNP : ∀ P ∈ T, 2 ≤ Ideal.absNorm P ∧ p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨h1, h2, _⟩ := hT2 P hP
    have a : Ideal.absNorm P ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have b : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact h1.ne_top
    refine ⟨by omega, ?_⟩
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 ((Finset.dvd_prod_of_mem _ hP).trans hprod)
    have hk0 : k ≠ 0 := by rintro rfl; rw [pow_zero] at hk; exact b hk
    rw [hk]; exact Nat.le_self_pow hk0 p
  have hTcard : T.card ≤ finrank ℚ K := by
    have h1 : p ^ T.card ≤ ∏ P ∈ T, Ideal.absNorm P :=
      Finset.pow_card_le_prod _ _ _ fun P hP => (hNP P hP).2
    have h2 : ∏ P ∈ T, Ideal.absNorm P ≤ p ^ finrank ℚ K :=
      Nat.le_of_dvd (pow_pos hp.pos _) hprod
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 (h1.trans h2)

  have hcover : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n →
      ∃ P ∈ T, Ideal.absNorm P ∣ n ∧ ∃ J, Ideal.absNorm J = n / Ideal.absNorm P ∧ I = P * J := by
    intro I hI
    have key : I ⊔ Ideal.span {q} ≠ ⊤ := by
      intro htop
      have hcard : Nat.card (𝓞 K ⧸ I) = n := by
        rw [← hI, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by omega)
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 K ⧸ I) p (hcard ▸ hpn)
      have h1 : (1 : 𝓞 K) ∈ I ⊔ Ideal.span {q} := htop ▸ Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      have hu : Ideal.Quotient.mk I r * (p : 𝓞 K ⧸ I) = 1 := by
        have := congrArg (Ideal.Quotient.mk I) hab
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, map_one] at this
        simpa [hqdef] using this
      have hpy : (p : 𝓞 K ⧸ I) * y = 0 := by
        rw [← nsmul_eq_mul, ← hy]; exact addOrderOf_nsmul_eq_zero y
      have hy0 : y = 0 := by
        calc y = (Ideal.Quotient.mk I r * (p : 𝓞 K ⧸ I)) * y := by rw [hu, one_mul]
          _ = Ideal.Quotient.mk I r * ((p : 𝓞 K ⧸ I) * y) := by ring
          _ = 0 := by rw [hpy, mul_zero]
      rw [hy0, addOrderOf_zero] at hy
      exact hp.one_lt.ne hy
    obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ key
    have hPT : P ∈ T := by
      have : P ∈ (↑T : Set (Ideal (𝓞 K))) := by
        rw [hT]; exact ⟨hPmax.isPrime, le_trans le_sup_right hPle⟩
      exact this
    obtain ⟨J, rfl⟩ := Ideal.dvd_iff_le.2 (le_trans le_sup_left hPle)
    rw [map_mul] at hI
    have hP0 : 0 < Ideal.absNorm P := by have := hNP P hPT; omega
    refine ⟨P, hPT, ⟨_, hI.symm⟩, J, ?_, rfl⟩
    rw [← hI, Nat.mul_div_cancel_left _ hP0]

  classical
  let T' := T.filter (fun P => Ideal.absNorm P ∣ n)
  let F := T'.biUnion (fun P =>
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n / Ideal.absNorm P)).toFinset.image (P * ·))
  have hsub : {I : Ideal (𝓞 K) | Ideal.absNorm I = n} ⊆ ↑F := by
    intro I hI
    obtain ⟨P, hPT, hdvd, J, hJ, rfl⟩ := hcover I hI
    simp only [F, T', Finset.coe_biUnion, Finset.coe_filter, Set.mem_iUnion, Finset.coe_image,
      Set.Finite.coe_toFinset, Set.mem_image, Set.mem_setOf_eq]
    exact ⟨P, ⟨hPT, hdvd⟩, J, hJ, rfl⟩
  have hΩ : 1 ≤ (Nat.primeFactorsList n).length := by
    have : Nat.primeFactorsList n ≠ [] := by
      rw [Ne, Nat.primeFactorsList_eq_nil]; omega
    exact List.length_pos_iff.2 this
  have hterm : ∀ P ∈ T', (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K)
      (n / Ideal.absNorm P)).toFinset.card ≤
        finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := by
    intro P hP
    obtain ⟨hPT, hdvd⟩ := Finset.mem_filter.1 hP
    obtain ⟨h2, _⟩ := hNP P hPT
    obtain ⟨m, hm⟩ := hdvd
    have hm0 : m ≠ 0 := by rintro rfl; omega
    have hmdiv : n / Ideal.absNorm P = m := by rw [hm, Nat.mul_div_cancel_left _ (by omega)]
    rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _), hmdiv]
    have hmlt : m < n := by
      rw [hm]; have : 1 * m < Ideal.absNorm P * m := by
        apply Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      omega
    refine (ih m hmlt (Nat.one_le_iff_ne_zero.2 hm0)).trans (Nat.pow_le_pow_right hd ?_)
    have hlen := (Nat.perm_primeFactorsList_mul (a := Ideal.absNorm P) (b := m)
      (by omega) hm0).length_eq
    rw [← hm, List.length_append] at hlen
    have : 1 ≤ (Nat.primeFactorsList (Ideal.absNorm P)).length := by
      have : Nat.primeFactorsList (Ideal.absNorm P) ≠ [] := by
        rw [Ne, Nat.primeFactorsList_eq_nil]; omega
      exact List.length_pos_iff.2 this
    omega
  calc {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard ≤ (↑F : Set (Ideal (𝓞 K))).ncard :=
        Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F
    _ ≤ ∑ P ∈ T', ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K)
          (n / Ideal.absNorm P)).toFinset.image (P * ·)).card := Finset.card_biUnion_le
    _ ≤ ∑ P ∈ T', (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) (n / Ideal.absNorm P)).toFinset.card :=
        Finset.sum_le_sum fun P _ => Finset.card_image_le
    _ ≤ ∑ P ∈ T', finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := Finset.sum_le_sum hterm
    _ = T'.card * finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) := by simp
    _ ≤ finrank ℚ K * finrank ℚ K ^ ((Nat.primeFactorsList n).length - 1) :=
        Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hTcard)
    _ = finrank ℚ K ^ (Nat.primeFactorsList n).length := by
        rw [← pow_succ']; congr 1; omega
open NumberField Formalism.SLP.P.CountO
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.SLP.P.CountO NumberField
open scoped nonZeroDivisors
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : IdealNormLeCount := by
  intro K _ _ x hx
  classical
  set d := finrank ℚ K
  have hd : 1 ≤ d := Module.finrank_pos
  let F := (Finset.Icc 1 ⌊x⌋₊).biUnion (fun n =>
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset)
  have hsub : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x} ⊆ ↑F := by
    rintro I ⟨hI, hx'⟩
    have h0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    simp only [F, Finset.coe_biUnion, Set.mem_iUnion, Finset.coe_Icc, Set.mem_Icc,
      Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨Ideal.absNorm I, ⟨by omega, Nat.le_floor hx'⟩, rfl⟩
  refine ⟨F.finite_toSet.subset hsub, ?_⟩
  have hL : 0 ≤ Real.logb 2 d := Real.logb_nonneg (by norm_num) (by exact_mod_cast hd)
  have hx0 : (0:ℝ) < x := by linarith
  have h1 : (({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ x}.ncard : ℕ) : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast (Set.ncard_le_ncard hsub F.finite_toSet).trans (Set.ncard_coe_finset F).le
  have h2 : (F.card : ℝ) ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h3 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) ≤ x ^ Real.logb 2 d := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
    rw [← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOf_absNorm_eq _)]
    have e1 : (({I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard : ℕ) : ℝ) ≤ (d : ℝ) ^ (Nat.primeFactorsList n).length := by
      exact_mod_cast normCount_lemma K n hn1
    have e2 := Formalism.SLP.Final.omegaPow d n hd hn1
    have e3 : (n : ℝ) ^ Real.logb 2 d ≤ x ^ Real.logb 2 d :=
      Real.rpow_le_rpow (by positivity) ((Nat.cast_le.2 hn2).trans (Nat.floor_le hx0.le)) hL
    linarith
  have h4 : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset.card : ℝ) ≤
      (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d := by
    refine (Finset.sum_le_sum h3).trans ?_
    simp
  have h5 : (⌊x⌋₊ : ℝ) * x ^ Real.logb 2 d ≤ x * x ^ Real.logb 2 d :=
    mul_le_mul_of_nonneg_right (Nat.floor_le hx0.le) (by positivity)
  rw [Real.rpow_add hx0, Real.rpow_one]
  linarith
end Formalism.HermitianLatticeCounting.P
