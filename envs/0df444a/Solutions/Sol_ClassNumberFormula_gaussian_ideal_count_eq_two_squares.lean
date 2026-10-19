-- Prove2me | solution 1 for ClassNumberFormula.gaussian_ideal_count_eq_two_squares
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:04:32.166818+00:00
-- url     : https://prove2.me/submissions/fb9f0145-50b8-4277-9e82-1e93c3e4031e

import Mathlib

open NumberField NumberField.InfinitePlace NumberField.Units Filter Topology Real



namespace CNGI

variable {K : Type*} [Field K] [NumberField K]

lemma prim (i : K) (hi : i ^ 2 = -1) : IsPrimitiveRoot i 4 := by
  apply IsPrimitiveRoot.mk_of_lt i (by norm_num)
  · calc i ^ 4 = (i ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hi]; norm_num
  · intro l hl0 hl4
    interval_cases l
    · intro h; rw [pow_one] at h; rw [h] at hi; norm_num at hi
    · rw [hi]; norm_num
    · intro h
      have : i ^ 3 = -i := by rw [pow_succ, hi]; ring
      rw [this] at h
      have h2 : i = -1 := by linear_combination -h
      rw [h2] at hi; norm_num at hi

section
variable (z : 𝓞 K) (hz : z ^ 2 = -1)
include hz

lemma e_inj (a b c d : ℤ) (h : (a : 𝓞 K) + b * z = c + d * z) : a = c ∧ b = d := by
  have h1 : ((a - c : ℤ) : 𝓞 K) = (d - b : ℤ) * z := by push_cast; linear_combination h
  have h2 : (((a - c) ^ 2 : ℤ) : 𝓞 K) = -(((d - b) ^ 2 : ℤ) : 𝓞 K) := by
    push_cast
    rw [show ((a : 𝓞 K) - c) ^ 2 = ((a - c : ℤ) : 𝓞 K) ^ 2 by push_cast; ring, h1]
    push_cast
    linear_combination ((d : 𝓞 K) - b) ^ 2 * hz
  rw [← Int.cast_neg] at h2
  have h3 := Int.cast_injective (α := 𝓞 K) h2
  constructor <;> nlinarith [sq_nonneg (a - c), sq_nonneg (d - b)]

end

section
variable [IsCyclotomicExtension {4} ℚ K] {i : K} (hp : IsPrimitiveRoot i 4)

lemma toInt_sq (hi : i ^ 2 = -1) : hp.toInteger ^ 2 = -1 := by
  ext
  have h : ((hp.toInteger : 𝓞 K) : K) = i := rfl
  simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_one] at h ⊢
  rw [h, hi]

lemma dim2 : hp.integralPowerBasis.dim = 2 := by
  rw [IsPrimitiveRoot.integralPowerBasis_dim]; decide

noncomputable def bas : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  hp.integralPowerBasis.basis.reindex (finCongr (dim2 hp))

lemma bas0 : bas hp 0 = 1 := by
  simp [bas, Module.Basis.reindex_apply, PowerBasis.coe_basis]

lemma bas1 : bas hp 1 = hp.toInteger := by
  simp [bas, Module.Basis.reindex_apply, PowerBasis.coe_basis]

lemma coords (x : 𝓞 K) : ∃ a b : ℤ, x = a + b * hp.toInteger := by
  refine ⟨(bas hp).repr x 0, (bas hp).repr x 1, ?_⟩
  conv_lhs => rw [← (bas hp).sum_repr x]
  rw [Fin.sum_univ_two, bas0, bas1, zsmul_eq_mul, zsmul_eq_mul, mul_one]

lemma repr_comb (c d : ℤ) :
    (bas hp).repr ((c : 𝓞 K) + d * hp.toInteger) 0 = c ∧
    (bas hp).repr ((c : 𝓞 K) + d * hp.toInteger) 1 = d := by
  have : (c : 𝓞 K) + d * hp.toInteger = c • bas hp 0 + d • bas hp 1 := by
    rw [bas0, bas1, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  rw [this, map_add, map_zsmul, map_zsmul, Module.Basis.repr_self, Module.Basis.repr_self]
  simp

lemma norm_eq (hi : i ^ 2 = -1) (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) + b * hp.toInteger) = a ^ 2 + b ^ 2 := by
  classical
  rw [Algebra.norm_eq_matrix_det (bas hp), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, bas0, bas1, mul_one]
  have e2 : ((a : 𝓞 K) + b * hp.toInteger) * hp.toInteger = ((-b : ℤ) : 𝓞 K) + (a : ℤ) * hp.toInteger := by
    push_cast; linear_combination (b : 𝓞 K) * toInt_sq hp hi
  rw [e2, (repr_comb hp a b).1, (repr_comb hp a b).2, (repr_comb hp (-b) a).1, (repr_comb hp (-b) a).2]
  ring

end

lemma cyc (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) (i : K)
    (hi : i ^ 2 = -1) : IsCyclotomicExtension {4} ℚ K := by
  have hprim : IsPrimitiveRoot i 4 := prim i hi
  have hnot : ∀ q : ℚ, algebraMap ℚ K q ≠ i := by
    intro q hq
    have : algebraMap ℚ K (q ^ 2) = algebraMap ℚ K (-1) := by
      rw [map_pow, hq, hi, map_neg, map_one]
    have h2 := (algebraMap ℚ K).injective this
    nlinarith [sq_nonneg q]
  have htop : IntermediateField.adjoin ℚ {i} = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', hK]
    have hd : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) ∣ 2 := by
      rw [← hK, ← IntermediateField.finrank_top' (F := ℚ) (E := K)]
      exact IntermediateField.finrank_dvd_of_le_right le_top
    have hne : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) ≠ 1 := by
      rw [Ne, IntermediateField.finrank_eq_one_iff, IntermediateField.adjoin_simple_eq_bot_iff,
        IntermediateField.mem_bot]
      rintro ⟨q, hq⟩
      exact hnot q hq
    have hpos : 0 < Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) := Module.finrank_pos
    have := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Module.finrank ℚ (IntermediateField.adjoin ℚ {i}) <;> simp_all
  have halg : Algebra.adjoin ℚ {i} = ⊤ :=
    (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic i)).mp htop
  rw [IsCyclotomicExtension.iff_singleton]
  refine ⟨⟨i, hprim⟩, fun x => ?_⟩
  have : x ∈ Algebra.adjoin ℚ {i} := by rw [halg]; trivial
  refine Algebra.adjoin_mono ?_ this
  intro b hb
  rw [Set.mem_singleton_iff] at hb
  subst hb
  exact hprim.pow_eq_one

lemma unit_cases (c d : ℤ) (h : c ^ 2 + d ^ 2 = 1) :
    (c = 1 ∧ d = 0) ∨ (c = -1 ∧ d = 0) ∨ (c = 0 ∧ d = 1) ∨ (c = 0 ∧ d = -1) := by
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg d, sq_nonneg (c - 1)]
  have hc2 : -1 ≤ c := by nlinarith [sq_nonneg d, sq_nonneg (c + 1)]
  have hd1 : d ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg (d - 1)]
  have hd2 : -1 ≤ d := by nlinarith [sq_nonneg c, sq_nonneg (d + 1)]
  interval_cases c <;> interval_cases d <;> simp_all

theorem main (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n} := by
  classical
  obtain ⟨i, hi⟩ := hi
  have := cyc K hK i hi
  have hp := prim i hi
  have hz := toInt_sq hp hi
  have hpid : IsPrincipalIdealRing (𝓞 K) := by
    have hc : InfinitePlace.nrComplexPlaces K = 1 := by
      rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4)]; decide
    have hdisc : discr K = -4 := by
      have ht : Nat.totient 4 = 2 := by decide
      have hp' : Nat.primeFactors 4 = {2} := by
        rw [show (4 : ℕ) = 2 ^ 2 by rfl, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
      rw [IsCyclotomicExtension.Rat.discr 4 K, ht, hp']; norm_num
    apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    rw [hdisc, hc, hK]
    norm_num [Nat.factorial]
    nlinarith [Real.pi_gt_three]
  set z := hp.toInteger with hzdef
  have habs : ∀ a b : ℤ, Ideal.absNorm (Ideal.span {(a : 𝓞 K) + b * z}) = (a ^ 2 + b ^ 2).natAbs := by
    intro a b; rw [Ideal.absNorm_span_singleton, norm_eq hp hi]
  have hmul : ∀ a b c d : ℤ, ((a : 𝓞 K) + b * z) * (c + d * z) =
      ((a * c - b * d : ℤ) : 𝓞 K) + ((a * d + b * c : ℤ) : 𝓞 K) * z := by
    intro a b c d; push_cast; linear_combination (b : 𝓞 K) * d * hz
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun p => ⟨Ideal.span {(p.1.1 : 𝓞 K) + p.1.2 * z}, ?_⟩) ⟨?_, ?_⟩)
  · rw [habs, p.2.2.2]; simp
  · rintro ⟨⟨a, b⟩, ha, hb, hab⟩ ⟨⟨a', b'⟩, ha', hb', hab'⟩ heq
    simp only [Subtype.mk.injEq] at heq
    rw [Ideal.span_singleton_eq_span_singleton] at heq
    obtain ⟨u, hu⟩ := heq
    obtain ⟨c, d, hcd⟩ := coords hp (u : 𝓞 K)
    have hcd1 : c ^ 2 + d ^ 2 = 1 := by
      have h1 := habs c d
      rw [← hcd, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top] at h1
      have : 0 ≤ c ^ 2 + d ^ 2 := by positivity
      omega
    rw [hcd, hmul] at hu
    obtain ⟨e1, e2⟩ := e_inj z hz _ _ _ _ hu
    simp only at ha hb ha' hb'
    rcases unit_cases c d hcd1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Subtype.mk.injEq, Prod.mk.injEq] <;> constructor <;> linarith
  · rintro ⟨I, hI⟩
    obtain ⟨g, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
    obtain ⟨a, b, rfl⟩ := coords hp g
    have hn' : a ^ 2 + b ^ 2 = n := by
      have h1 := habs a b
      change Ideal.absNorm (Ideal.span {(a : 𝓞 K) + b * z}) = n at hI
      rw [hI] at h1
      have : 0 ≤ a ^ 2 + b ^ 2 := by positivity
      omega
    have hne : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩; simp at hn'; omega
    have key : ∀ c d : ℤ, IsUnit ((c : 𝓞 K) + d * z) → ∀ a' b' : ℤ, 0 < a' → 0 ≤ b' →
        ((a : 𝓞 K) + b * z) * (c + d * z) = a' + b' * z →
        ∃ p : {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n},
          Ideal.span {(p.1.1 : 𝓞 K) + p.1.2 * z} = Submodule.span (𝓞 K) {(a : 𝓞 K) + b * z} := by
      intro c d hu a' b' ha' hb' he
      have hu' : c ^ 2 + d ^ 2 = 1 := by
        have h1 := habs c d
        rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.absNorm_top] at h1
        have : 0 ≤ c ^ 2 + d ^ 2 := by positivity
        omega
      refine ⟨⟨(a', b'), ha', hb', ?_⟩, ?_⟩
      · rw [hmul] at he
        obtain ⟨e1, e2⟩ := e_inj z hz _ _ _ _ he
        rw [← hn', ← e1, ← e2]
        linear_combination (a ^ 2 + b ^ 2) * hu'
      · simp only
        rw [← he]
        exact Ideal.span_singleton_mul_right_unit hu _
    have hzu : IsUnit z := IsUnit.of_mul_eq_one (-z) (by linear_combination -hz)
    have u1 : IsUnit ((1 : ℤ) + (0 : ℤ) * z : 𝓞 K) := by simp
    have u2 : IsUnit ((-1 : ℤ) + (0 : ℤ) * z : 𝓞 K) := by simp
    have u3 : IsUnit ((0 : ℤ) + (1 : ℤ) * z : 𝓞 K) := by simpa using hzu
    have u4 : IsUnit ((0 : ℤ) + (-1 : ℤ) * z : 𝓞 K) := by simpa using hzu.neg
    have fin : ∃ p : {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n},
        Ideal.span {(p.1.1 : 𝓞 K) + p.1.2 * z} = Submodule.span (𝓞 K) {(a : 𝓞 K) + b * z} := by
      rcases lt_trichotomy 0 a with ha | ha | ha
      · rcases le_or_gt 0 b with hb | hb
        · exact key 1 0 u1 a b ha hb (by rw [hmul]; push_cast; ring)
        · exact key 0 1 u3 (-b) a (by linarith) ha.le (by rw [hmul]; push_cast; ring)
      · subst ha
        rcases lt_or_gt_of_ne (fun h : b = 0 => hne ⟨rfl, h⟩) with hb | hb
        · exact key 0 1 u3 (-b) 0 (by linarith) le_rfl (by rw [hmul]; push_cast; ring)
        · exact key 0 (-1) u4 b 0 hb le_rfl (by rw [hmul]; push_cast; ring)
      · rcases le_or_gt b 0 with hb | hb
        · exact key (-1) 0 u2 (-a) (-b) (by linarith) (by linarith) (by rw [hmul]; push_cast; ring)
        · exact key 0 (-1) u4 b (-a) hb (by linarith) (by rw [hmul]; push_cast; ring)
    obtain ⟨p, hp'⟩ := fin
    exact ⟨p, Subtype.ext hp'⟩

end CNGI

theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hi : ∃ i : K, i ^ 2 = -1) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {p : ℤ × ℤ // 0 < p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = n} :=
  CNGI.main K hK hi n hn
