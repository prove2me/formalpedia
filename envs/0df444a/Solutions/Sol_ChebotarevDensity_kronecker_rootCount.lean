-- Prove2me | solution 1 for ChebotarevDensity.kronecker_rootCount
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-01T14:35:21.849989+00:00
-- url     : https://prove2.me/submissions/fd8d421e-0eac-45b9-bc92-9fa02e6629be

import Definitions.Def_ChebotarevDensity_Aux
import Theorems.Thm_ChebotarevDensity_zetaPrimeSum_asymp

open Polynomial NumberField
open ChebotarevDensity

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Z2

open IsDedekindDomain UniqueFactorizationMonoid

section Generic

variable {L : Type} [Field L] [NumberField L]

private instance (P : HeightOneSpectrum (𝓞 L)) : NeZero P.asIdeal := ⟨P.ne_bot⟩

private lemma qP_prime (P : HeightOneSpectrum (𝓞 L)) : (Ideal.absNorm (P.asIdeal.under ℤ)).Prime :=
  Nat.absNorm_under_prime P.asIdeal

private noncomputable def qP (P : HeightOneSpectrum (𝓞 L)) : {p : ℕ // p.Prime} := ⟨_, qP_prime P⟩

private lemma under_eq_span (P : HeightOneSpectrum (𝓞 L)) :
    P.asIdeal.under ℤ = Ideal.span {((qP P : ℕ) : ℤ)} :=
  (Int.ideal_span_absNorm_eq_self _).symm

private lemma liesOver_qP (P : HeightOneSpectrum (𝓞 L)) :
    P.asIdeal.LiesOver (Ideal.span {((qP P : ℕ) : ℤ)}) := ⟨(under_eq_span P).symm⟩

private lemma liesOver_of_qP {p : {p : ℕ // p.Prime}} {P : HeightOneSpectrum (𝓞 L)} (h : qP P = p) :
    P.asIdeal.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) := by
  subst h; exact liesOver_qP P

private noncomputable def fibEquiv (p : {p : ℕ // p.Prime}) :
    {P : HeightOneSpectrum (𝓞 L) // qP P = p} ≃ Ideal.primesOver (Ideal.span {((p : ℕ) : ℤ)}) (𝓞 L) :=
  Equiv.ofBijective
    (fun P => ⟨P.1.asIdeal, P.1.isPrime, liesOver_of_qP P.2⟩)
    ⟨fun P Q h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)), by
      rintro ⟨I, hI, hlo⟩
      have hp : (Ideal.span {((p : ℕ) : ℤ)}) ≠ ⊥ := by
        simp [p.2.ne_zero]
      have hne : I ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hp ⟨hI, hlo⟩
      refine ⟨⟨⟨I, hI, hne⟩, ?_⟩, rfl⟩
      apply Subtype.ext
      have h1 : Ideal.span {((p : ℕ) : ℤ)} = I.under ℤ := hlo.over
      show Ideal.absNorm (I.under ℤ) = (p : ℕ)
      rw [← h1]
      simp⟩


private lemma norm_eq (P : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm P.asIdeal = (qP P : ℕ) ^ (P.asIdeal.inertiaDeg ℤ) := by
  have := liesOver_qP P
  have : Fact (qP P : ℕ).Prime := ⟨(qP P).2⟩
  have : (Ideal.span {((qP P : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime _
  rw [Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal (qP P).2, Ideal.inertiaDeg'_eq_inertiaDeg]

private lemma inertiaDeg_pos (P : HeightOneSpectrum (𝓞 L)) : 0 < P.asIdeal.inertiaDeg ℤ :=
  Ideal.inertiaDeg_pos _ _

private instance fib_finite (p : {p : ℕ // p.Prime}) : Finite {P : HeightOneSpectrum (𝓞 L) // qP P = p} := by
  have : Finite (Ideal.primesOver (Ideal.span {((p : ℕ) : ℤ)}) (𝓞 L)) :=
    (Algebra.QuasiFinite.finite_primesOver _).to_subtype
  exact Finite.of_equiv _ (fibEquiv p).symm



private lemma card_factors_le {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) (hf : f.Monic) :
    (normalizedFactors f).toFinset.card ≤ f.natDegree := by
  classical
  have hmon : ∀ Q ∈ normalizedFactors f, Q.Monic := fun Q hQ => by
    have := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hQ
    exact this.2.1
  have hprod : (normalizedFactors f).prod = f := by
    have h1 := prod_normalizedFactors hf.ne_zero
    have h2 : (normalizedFactors f).prod.Monic := by simpa using monic_multiset_prod_of_monic (normalizedFactors f) id hmon
    exact eq_of_monic_of_associated h2 hf h1
  calc (normalizedFactors f).toFinset.card ≤ Multiset.card (normalizedFactors f) :=
        Multiset.toFinset_card_le _
    _ = ((normalizedFactors f).map (fun _ => 1)).sum := by simp
    _ ≤ ((normalizedFactors f).map natDegree).sum := by
        apply Multiset.sum_map_le_sum_map
        intro Q hQ
        have := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp hQ
        exact (this.1).natDegree_pos
    _ = f.natDegree := by
        rw [← natDegree_multiset_prod_of_monic _ hmon, hprod]


private lemma rootCount_eq (g : ℤ[X]) (hg : g.Monic) (p : ℕ) [Fact p.Prime] :
    ChebotarevDensity.rootCount g p =
      ((normalizedFactors (g.map (Int.castRingHom (ZMod p)))).toFinset.filter
        (fun Q => Q.natDegree = 1)).card := by
  classical
  set f := g.map (Int.castRingHom (ZMod p)) with hf
  have hfm : f.Monic := hg.map _
  unfold ChebotarevDensity.rootCount
  have key : Nat.card {x : ZMod p // f.IsRoot x} = Nat.card {Q // Q ∈ (normalizedFactors f).toFinset.filter
      (fun Q => Q.natDegree = 1)} := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨X - C x.1, ?_⟩) ⟨?_, ?_⟩)
    · simp only [Finset.mem_filter, Multiset.mem_toFinset]
      refine ⟨?_, natDegree_X_sub_C _⟩
      rw [Polynomial.mem_normalizedFactors_iff hfm.ne_zero]
      exact ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr x.2⟩
    · intro x y h
      have h1 := congrArg Subtype.val h
      simp only [sub_right_inj, C_inj] at h1
      exact Subtype.ext h1
    · rintro ⟨Q, hQ⟩
      simp only [Finset.mem_filter, Multiset.mem_toFinset] at hQ
      obtain ⟨hQ1, hQ2⟩ := hQ
      have hQ3 := (Polynomial.mem_normalizedFactors_iff hfm.ne_zero).mp hQ1
      have hQe := hQ3.2.1.eq_X_add_C hQ2
      have hX : X - C (-Q.coeff 0) = Q := by rw [hQe]; simp
      refine ⟨⟨-Q.coeff 0, ?_⟩, Subtype.ext hX⟩
      rw [← dvd_iff_isRoot, hX]
      exact hQ3.2.2
  rw [key, Nat.card_eq_fintype_card, Fintype.card_coe]



open RingOfIntegers in
private lemma fibre_sum (θ : 𝓞 L) (p : {p : ℕ // p.Prime}) [Fact (p : ℕ).Prime] (hp : ¬ (p : ℕ) ∣ exponent θ) (s : ℝ) :
    ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) =
      ∑ Q ∈ monicFactorsMod θ p, (((p : ℕ) : ℝ) ^ (-s)) ^ Q.natDegree := by
  let e : {P : HeightOneSpectrum (𝓞 L) // qP P = p} ≃ ↥(monicFactorsMod θ p) :=
    (fibEquiv p).trans (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp)
  rw [← Equiv.tsum_eq e.symm, tsum_fintype, ← Finset.sum_coe_sort (monicFactorsMod θ p)]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  have h1 : (e.symm Q).1.asIdeal = ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q : Ideal (𝓞 L)) :=
    congrArg Subtype.val ((fibEquiv p).apply_symm_apply ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm Q))
  have h2 := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp Q.2
  have h3 : (qP (e.symm Q).1 : ℕ) = p := congrArg Subtype.val (e.symm Q).2
  have h4 : Ideal.absNorm (e.symm Q).1.asIdeal = (p : ℕ) ^ Q.1.natDegree := by
    rw [norm_eq, h3, h1]
    exact congrArg _ h2
  rw [h4, Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg _), mul_comm, Real.rpow_mul_natCast (Nat.cast_nonneg _)]

private lemma sum_pow_bounds {ι : Type*} (T : Finset ι) (deg : ι → ℕ) (hdeg : ∀ Q ∈ T, 1 ≤ deg Q)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ((T.filter (fun Q => deg Q = 1)).card : ℝ) * t ≤ ∑ Q ∈ T, t ^ deg Q ∧
    ∑ Q ∈ T, t ^ deg Q ≤ ((T.filter (fun Q => deg Q = 1)).card : ℝ) * t + (T.card : ℝ) * t ^ 2 := by
  classical
  have hsplit : ∑ Q ∈ T, t ^ deg Q = ∑ Q ∈ T.filter (fun Q => deg Q = 1), t ^ deg Q +
      ∑ Q ∈ T.filter (fun Q => ¬ deg Q = 1), t ^ deg Q := (Finset.sum_filter_add_sum_filter_not T (fun Q => deg Q = 1) (fun Q => t ^ deg Q)).symm
  have hA : ∑ Q ∈ T.filter (fun Q => deg Q = 1), t ^ deg Q = ((T.filter (fun Q => deg Q = 1)).card : ℝ) * t := by
    rw [Finset.sum_congr rfl (g := fun _ => t) (fun Q hQ => by rw [(Finset.mem_filter.mp hQ).2, pow_one])]
    simp
  have hB0 : 0 ≤ ∑ Q ∈ T.filter (fun Q => ¬ deg Q = 1), t ^ deg Q :=
    Finset.sum_nonneg (fun Q _ => pow_nonneg h0 _)
  have hB1 : ∑ Q ∈ T.filter (fun Q => ¬ deg Q = 1), t ^ deg Q ≤ (T.card : ℝ) * t ^ 2 := by
    calc ∑ Q ∈ T.filter (fun Q => ¬ deg Q = 1), t ^ deg Q
        ≤ ∑ Q ∈ T.filter (fun Q => ¬ deg Q = 1), t ^ 2 := by
          refine Finset.sum_le_sum (fun Q hQ => ?_)
          obtain ⟨hQT, hQ1⟩ := Finset.mem_filter.mp hQ
          exact pow_le_pow_of_le_one h0 h1 (by have := hdeg Q hQT; omega)
      _ = ((T.filter (fun Q => ¬ deg Q = 1)).card : ℝ) * t ^ 2 := by simp
      _ ≤ (T.card : ℝ) * t ^ 2 := by
          have : (T.filter (fun Q => ¬ deg Q = 1)).card ≤ T.card := Finset.card_filter_le _ _
          have h2 : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h2
  constructor
  · rw [hsplit, hA]; linarith
  · rw [hsplit, hA]; linarith

open RingOfIntegers in
private lemma good_bound (θ : 𝓞 L) (g : ℤ[X]) (hg : g.Monic) (hmin : minpoly ℤ θ = g)
    (p : {p : ℕ // p.Prime}) [Fact (p : ℕ).Prime] (hp : ¬ (p : ℕ) ∣ exponent θ) {s : ℝ} (hs : 1 ≤ s) :
    (ChebotarevDensity.rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s) ≤
      ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) ∧
    ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) ≤
      (ChebotarevDensity.rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s) +
        (g.natDegree : ℝ) * (((p : ℕ) : ℝ)⁻¹) ^ 2 := by
  have hT : monicFactorsMod θ p = (normalizedFactors (g.map (Int.castRingHom (ZMod p)))).toFinset := by
    simp only [monicFactorsMod, hmin]
  have hgm : (g.map (Int.castRingHom (ZMod p))).Monic := hg.map _
  rw [fibre_sum θ p hp s, rootCount_eq g hg p, hT]
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have ht0 : 0 ≤ ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  have ht1 : ((p : ℕ) : ℝ) ^ (-s) ≤ ((p : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hinv1 : ((p : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have hdeg : ∀ Q ∈ (normalizedFactors (g.map (Int.castRingHom (ZMod p)))).toFinset, 1 ≤ Q.natDegree := by
    intro Q hQ
    have := (Polynomial.mem_normalizedFactors_iff hgm.ne_zero).mp (Multiset.mem_toFinset.mp hQ)
    exact this.1.natDegree_pos
  obtain ⟨b1, b2⟩ := sum_pow_bounds _ (fun Q : (ZMod p)[X] => Q.natDegree) hdeg ht0 (ht1.trans hinv1)
  refine ⟨b1, b2.trans ?_⟩
  have hcard : ((normalizedFactors (g.map (Int.castRingHom (ZMod p)))).toFinset.card : ℝ) ≤ g.natDegree := by
    have := card_factors_le (g.map (Int.castRingHom (ZMod p))) hgm
    rw [hg.natDegree_map] at this
    exact_mod_cast this
  have hsq : (((p : ℕ) : ℝ) ^ (-s)) ^ 2 ≤ (((p : ℕ) : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
  have : ((normalizedFactors (g.map (Int.castRingHom (ZMod p)))).toFinset.card : ℝ) * (((p : ℕ) : ℝ) ^ (-s)) ^ 2 ≤
      (g.natDegree : ℝ) * (((p : ℕ) : ℝ)⁻¹) ^ 2 := by
    exact mul_le_mul hcard hsq (sq_nonneg _) (Nat.cast_nonneg _)
  linarith

private lemma term_nonneg (s : ℝ) (P : HeightOneSpectrum (𝓞 L)) :
    0 ≤ ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _

private lemma term_le_one {s : ℝ} (hs : 0 ≤ s) (P : HeightOneSpectrum (𝓞 L)) :
    ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos _ (by linarith)
  have : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

private lemma fibre_le_card {s : ℝ} (hs : 0 ≤ s) (p : {p : ℕ // p.Prime}) :
    0 ≤ ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) ∧
    ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) ≤
      Nat.card {P : HeightOneSpectrum (𝓞 L) // qP P = p} := by
  have := Fintype.ofFinite {P : HeightOneSpectrum (𝓞 L) // qP P = p}
  rw [tsum_fintype]
  refine ⟨Finset.sum_nonneg (fun P _ => term_nonneg s P.1), ?_⟩
  calc _ ≤ ∑ _P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, (1 : ℝ) :=
        Finset.sum_le_sum (fun P _ => term_le_one hs P.1)
    _ = _ := by simp [Nat.card_eq_fintype_card]

private lemma rootCount_le (g : ℤ[X]) (hg : g.Monic) (p : ℕ) [Fact p.Prime] :
    ChebotarevDensity.rootCount g p ≤ g.natDegree := by
  rw [rootCount_eq g hg p]
  refine (Finset.card_filter_le _ _).trans ?_
  have := card_factors_le (g.map (Int.castRingHom (ZMod p))) (hg.map _)
  rwa [hg.natDegree_map] at this

private lemma summable_t {s : ℝ} (hs : 1 < s) :
    Summable (fun p : {p : ℕ // p.Prime} => ((p : ℕ) : ℝ) ^ (-s)) :=
  Nat.Primes.summable_rpow.mpr (by linarith)

private lemma summable_sq : Summable (fun p : {p : ℕ // p.Prime} => (((p : ℕ) : ℝ)⁻¹) ^ 2) := by
  have := (Nat.Primes.summable_rpow (r := -2)).mpr (by norm_num)
  refine this.congr (fun p => ?_)
  show _ = (((p : ℕ) : ℝ)⁻¹) ^ 2
  rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]

open RingOfIntegers in
private lemma main_compare (θ : 𝓞 L) (g : ℤ[X]) (hg : g.Monic) (hmin : minpoly ℤ θ = g)
    (hexp : exponent θ ≠ 0) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      |(∑' P : HeightOneSpectrum (𝓞 L), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) -
        ∑' p : {p : ℕ // p.Prime}, (ChebotarevDensity.rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s)| ≤ C := by
  classical
  set d : ℝ := (g.natDegree : ℝ) with hd
  let m : {p : ℕ // p.Prime} → ℝ := fun p => (Nat.card {P : HeightOneSpectrum (𝓞 L) // qP P = p} : ℝ)
  let w : {p : ℕ // p.Prime} → ℝ := fun p =>
    d * (((p : ℕ) : ℝ)⁻¹) ^ 2 + (if (p : ℕ) ∣ exponent θ then m p + d else 0)
  have hw : Summable w := by
    refine (summable_sq.mul_left d).add (summable_of_hasFiniteSupport ?_)
    refine Set.Finite.subset (Set.Finite.preimage (f := fun p : {p : ℕ // p.Prime} => (p : ℕ))
      (Subtype.val_injective.injOn) (Nat.divisors (exponent θ)).finite_toSet) ?_
    intro p hp
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hp
    obtain ⟨h1, _⟩ := hp
    simp [Nat.mem_divisors, h1, hexp]
  refine ⟨∑' p, w p, fun s hs => ?_⟩
  have hs0 : (0 : ℝ) ≤ s := by linarith
  set hf : {p : ℕ // p.Prime} → ℝ := fun p =>
    ∑' P : {P : HeightOneSpectrum (𝓞 L) // qP P = p}, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ) ^ (-s) with hhf
  set rt : {p : ℕ // p.Prime} → ℝ := fun p =>
    (ChebotarevDensity.rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s) with hrt
  have hrt_le : ∀ p : {p : ℕ // p.Prime}, rt p ≤ d * ((p : ℕ) : ℝ) ^ (-s) := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have h1 : (ChebotarevDensity.rootCount g p : ℝ) ≤ d := by
      rw [hd]; exact_mod_cast rootCount_le g hg p
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hrt_nn : ∀ p : {p : ℕ // p.Prime}, 0 ≤ rt p := fun p =>
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hu : ∀ p : {p : ℕ // p.Prime}, ‖hf p - rt p‖ ≤ w p := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hsq : 0 ≤ d * (((p : ℕ) : ℝ)⁻¹) ^ 2 := by positivity
    by_cases hdvd : (p : ℕ) ∣ exponent θ
    · have hwp : w p = d * (((p : ℕ) : ℝ)⁻¹) ^ 2 + (m p + d) := by simp [w, hdvd]
      obtain ⟨c1, c2⟩ := fibre_le_card (L := L) hs0 p
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
      have ht1 : ((p : ℕ) : ℝ) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
      have h1 : rt p ≤ d := by
        have := hrt_le p
        have hd0 : 0 ≤ d := Nat.cast_nonneg _
        nlinarith
      rw [Real.norm_eq_abs, abs_le]
      have hm : m p = (Nat.card {P : HeightOneSpectrum (𝓞 L) // qP P = p} : ℝ) := rfl
      have := hrt_nn p
      constructor <;> linarith
    · have hwp : w p = d * (((p : ℕ) : ℝ)⁻¹) ^ 2 := by simp [w, hdvd]
      obtain ⟨b1, b2⟩ := good_bound θ g hg hmin p hdvd hs.le
      rw [Real.norm_eq_abs, abs_le, hwp]
      have := hrt_nn p
      constructor <;> linarith
  have hsum_rt : Summable rt :=
    Summable.of_nonneg_of_le hrt_nn hrt_le ((summable_t hs).mul_left d)
  have hsum_hf : Summable hf := by
    refine Summable.of_nonneg_of_le (fun p => (fibre_le_card (L := L) hs0 p).1) (fun p => ?_)
      (hw.add ((summable_t hs).mul_left d))
    have := (abs_le.mp (hu p)).2
    have := hrt_le p
    show hf p ≤ w p + d * ((p : ℕ) : ℝ) ^ (-s)
    linarith
  let e := Equiv.sigmaFiberEquiv (qP : HeightOneSpectrum (𝓞 L) → {p : ℕ // p.Prime})
  have hsumF : Summable (fun P : HeightOneSpectrum (𝓞 L) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun x => term_nonneg s (e x))).mpr ⟨fun p => Summable.of_finite, ?_⟩
    exact hsum_hf
  have heq : (∑' P : HeightOneSpectrum (𝓞 L), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) = ∑' p, hf p := by
    rw [← e.tsum_eq]
    refine Summable.tsum_sigma' (fun p => Summable.of_finite) ?_
    exact e.summable_iff.mpr hsumF
  rw [heq, ← Summable.tsum_sub hsum_hf hsum_rt, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded hw.hasSum hu


end Generic

section Concrete

private abbrev LL (g : ℤ[X]) := AdjoinRoot (g.map (Int.castRingHom ℚ))

variable {g : ℤ[X]} [Fact (Irreducible (g.map (Int.castRingHom ℚ)))]

private lemma root_isIntegral (hg : g.Monic) : IsIntegral ℤ (AdjoinRoot.root (g.map (Int.castRingHom ℚ))) := by
  refine ⟨g, hg, ?_⟩
  rw [← Polynomial.aeval_def]
  have h := aeval_map_algebraMap ℚ (AdjoinRoot.root (g.map (Int.castRingHom ℚ))) g
  rw [← h]
  exact AdjoinRoot.eval₂_root _

private instance (g : ℤ[X]) [Fact (Irreducible (g.map (Int.castRingHom ℚ)))] : NumberField (LL g) where
  to_charZero := inferInstance
  to_finiteDimensional := (AdjoinRoot.powerBasis (Fact.out : Irreducible (g.map (Int.castRingHom ℚ))).ne_zero).finite

private noncomputable def theta (hg : g.Monic) : 𝓞 (LL g) := ⟨AdjoinRoot.root _, root_isIntegral hg⟩

private lemma θ_int (hg : g.Monic) : IsIntegral ℤ (theta hg) := RingOfIntegers.isIntegral _

private lemma minpoly_theta (hg : g.Monic) : minpoly ℤ (theta hg) = g := by
  have h1 := minpoly.isIntegrallyClosed_eq_field_fractions ℚ (LL g) (R := ℤ) (θ_int hg)
  have h2 : minpoly ℚ (algebraMap (𝓞 (LL g)) (LL g) (theta hg)) = g.map (Int.castRingHom ℚ) := by
    have := AdjoinRoot.minpoly_root (Fact.out : Irreducible (g.map (Int.castRingHom ℚ))).ne_zero
    rw [Polynomial.Monic.leadingCoeff (hg.map _)] at this
    rw [inv_one, C_1, mul_one] at this; exact this
  rw [h2] at h1
  exact (Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ) h1).symm

private lemma mem_adjoin_theta_iff (hg : g.Monic) (x : 𝓞 (LL g)) :
    x ∈ Algebra.adjoin ℤ {theta hg} ↔
      (x : LL g) ∈ Algebra.adjoin ℤ {(AdjoinRoot.root (g.map (Int.castRingHom ℚ)))} := by
  let f : 𝓞 (LL g) →ₐ[ℤ] LL g := IsScalarTower.toAlgHom ℤ (𝓞 (LL g)) (LL g)
  have hf : Function.Injective f := Subtype.val_injective
  have h := AlgHom.map_adjoin f {theta hg}
  rw [Set.image_singleton] at h
  have : f (theta hg) = AdjoinRoot.root (g.map (Int.castRingHom ℚ)) := rfl
  rw [this] at h
  rw [← h, Subalgebra.mem_map]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := hf hyx
    exact this ▸ hy

private lemma exponent_ne_zero (hg : g.Monic) : RingOfIntegers.exponent (theta hg) ≠ 0 := by
  set B := AdjoinRoot.powerBasis (Fact.out : Irreducible (g.map (Int.castRingHom ℚ))).ne_zero with hB
  have hint : IsIntegral ℤ B.gen := by
    simpa [hB, AdjoinRoot.powerBasis_gen] using root_isIntegral hg
  have hD : IsIntegral ℤ (Algebra.discr ℚ B.basis) :=
    Algebra.discr_isIntegral ℚ (fun i => by simpa using hint.pow i)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hD
  have hn0 : n ≠ 0 := by
    intro h0
    have := Algebra.discr_not_zero_of_basis ℚ B.basis
    exact this (hn.symm.trans (by rw [h0, map_zero]))
  have hmem : (n : 𝓞 (LL g)) ∈ conductor ℤ (theta hg) := by
    intro b
    show _ ∈ Algebra.adjoin ℤ {theta hg}
    rw [mem_adjoin_theta_iff]
    have := Algebra.discr_mul_isIntegral_mem_adjoin (R := ℤ) (K := ℚ) hint (z := (b : LL g)) 
      b.isIntegral_coe
    have e : (((n : 𝓞 (LL g)) * b : 𝓞 (LL g)) : LL g) = Algebra.discr ℚ B.basis • (b : LL g) := by
      rw [← hn, Rat.smul_def]
      simp
    rw [e]
    have h2 : B.gen = AdjoinRoot.root (g.map (Int.castRingHom ℚ)) := by
      simp [hB, AdjoinRoot.powerBasis_gen]
    rw [h2] at this
    exact this
  intro h
  unfold RingOfIntegers.exponent at h
  rw [Ideal.absNorm_eq_zero_iff] at h
  have : n ∈ Ideal.under ℤ (conductor ℤ (theta hg)) := by
    rw [Ideal.mem_comap]; simpa using hmem
  rw [h] at this
  simp at this
  exact hn0 this


end Concrete

end Z2

theorem solution (g : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in nhdsWithin 1 (Set.Ioi 1),
      |(∑' p : {p : ℕ // p.Prime}, (rootCount g p : ℝ) * ((p : ℕ) : ℝ) ^ (-s)) -
        Real.log (1 / (s - 1))| ≤ C := by
  have : Fact (Irreducible (g.map (Int.castRingHom ℚ))) := ⟨hirr⟩
  obtain ⟨C0, h0⟩ := ChebotarevDensity.zetaPrimeSum_asymp (Z2.LL g)
  obtain ⟨C1, h1⟩ := Z2.main_compare (Z2.theta hg) g hg (Z2.minpoly_theta hg) (Z2.exponent_ne_zero hg)
  refine ⟨C1 + C0, ?_⟩
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1
  have h2 := h1 s hs1
  rw [abs_le] at *
  constructor <;> linarith [h2.1, h2.2, hs0.1, hs0.2]
