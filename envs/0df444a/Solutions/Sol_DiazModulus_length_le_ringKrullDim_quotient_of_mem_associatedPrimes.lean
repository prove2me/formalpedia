-- Prove2me | solution 1 for DiazModulus.length_le_ringKrullDim_quotient_of_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T18:21:31.422486+00:00
-- url     : https://prove2.me/submissions/8d51a7bd-fbf6-4738-89d1-e9e31cb027fa

import Mathlib

open RingTheory.Sequence IsLocalRing Pointwise

/-! # A weakly regular sequence in the maximal ideal is at most `dim A/𝔭` long, for `𝔭 ∈ Ass M`

Induction on the sequence `x :: rs`. Write `𝔭 = ann m` with `m ≠ 0`. Since `x ∈ 𝔪` is `M`-regular,
Krull's intersection theorem (`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) gives a largest `j` with
`m ∈ x^j M`; writing `m = x^j m'` gives `m' ∉ xM` with `ann m' = ann m = 𝔭`, because `x^j` is
`M`-regular. The class of `m'` in `M/xM` is nonzero, so it lies under an associated prime `q` of
`M/xM` (`exists_le_isAssociatedPrime_of_isNoetherianRing`), with `𝔭 ≤ q` and `x ∈ q`, while `x ∉ 𝔭`
(otherwise `x m' = 0`, so `m' = 0`). Then `x` is a nonzerodivisor of the domain `A/𝔭`, and `A/q` is a
quotient of `(A/𝔭)/(x)`, so `dim A/q + 1 ≤ dim A/𝔭` (`ringKrullDim_quotient_succ_le_of_nonZeroDivisor`).
The induction hypothesis for `M/xM`, `rs` and `q` gives `|rs| ≤ dim A/q`, hence `|x :: rs| ≤ dim A/𝔭`.
For the empty sequence, `A/𝔭` is nontrivial, so its dimension is at least `0`. -/

namespace C12_DL

/-- Krull's intersection step: replace a witness `m` by `m'` with the same annihilator and
`m' ∉ xM`. -/
lemma exists_good_witness {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular M x) {m : M} (hm : m ≠ 0) :
    ∃ m' : M, m' ∉ x • (⊤ : Submodule A M) ∧ ∀ a : A, a • m = 0 ↔ a • m' = 0 := by
  have hpow : ∀ (j : ℕ) (m : M), m ∈ (Ideal.span {x}) ^ j • (⊤ : Submodule A M) ↔
      ∃ m' : M, x ^ j • m' = m := fun j m => by
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hne : Ideal.span {x} ≠ ⊤ := fun h =>
    (mem_maximalIdeal x).mp hx (Ideal.span_singleton_eq_top.mp h)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {x}) hne
  have hex : ∃ i, m ∉ (Ideal.span {x}) ^ i • (⊤ : Submodule A M) := by
    by_contra h
    push Not at h
    apply hm
    have : m ∈ ⨅ i, (Ideal.span {x}) ^ i • (⊤ : Submodule A M) := Submodule.mem_iInf _ |>.mpr h
    rw [hK] at this
    exact (Submodule.mem_bot A).mp this
  classical
  have hi := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, m ∈ (Ideal.span {x}) ^ k • (⊤ : Submodule A M) :=
    fun k hk => not_not.mp (Nat.find_min hex hk)
  generalize Nat.find hex = i at hi hmin
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (by
    rintro rfl; exact hi (by simp))
  obtain ⟨m', hm'⟩ := (hpow j m).mp (hmin j (by omega))
  refine ⟨m', ?_, ?_⟩
  · intro hmem
    obtain ⟨m'', -, hm''⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    apply hi
    rw [hpow]
    exact ⟨m'', by rw [pow_succ, mul_smul, hm'', hm']⟩
  · intro a
    rw [← hm', smul_comm a (x ^ j) m']
    constructor
    · intro h
      exact (hreg.pow j) (show x ^ j • (a • m') = x ^ j • (0 : M) by rw [smul_zero]; exact h)
    · intro h; rw [h, smul_zero]

end C12_DL

open C12_DL in
theorem solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (rs : List A) {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hreg : RingTheory.Sequence.IsWeaklyRegular M rs) (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal A)
    (p : Ideal A) (hp : p ∈ associatedPrimes A M) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) := by
  induction rs generalizing M p with
  | nil =>
    have : p.IsPrime := hp.isPrime
    simpa using ringKrullDim_nonneg_of_nontrivial (R := A ⧸ p)
  | cons x rs ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hx, hrs⟩ := hreg
    have hxm : x ∈ maximalIdeal A := hmem x (List.mem_cons_self ..)
    obtain ⟨hpprime, m, hpm⟩ := (isAssociatedPrime_iff (R := A) (M := M)).mp hp
    have hm0 : m ≠ 0 := by
      rintro rfl
      apply hpprime.ne_top
      rw [hpm, eq_top_iff]
      intro a _
      rw [Submodule.mem_colon_singleton]
      simp
    obtain ⟨m', hm'x, hann⟩ := exists_good_witness hxm hx hm0
    have hpm' : ∀ a, a ∈ p ↔ a • m' = 0 := by
      intro a
      rw [hpm, Submodule.mem_colon_singleton, Submodule.mem_bot, hann]
    let mbar : QuotSMulTop x M := Submodule.Quotient.mk m'
    have hmbar : mbar ≠ 0 := by
      simpa [mbar, Ne, Submodule.Quotient.mk_eq_zero] using hm'x
    obtain ⟨q, hq, hqle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A mbar hmbar
    have hpq : p ≤ q := by
      intro a ha
      apply hqle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      simp only [mbar]
      rw [← Submodule.Quotient.mk_smul, (hpm' a).mp ha, Submodule.Quotient.mk_zero]
    have hxq : x ∈ q := by
      apply hqle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact Module.mem_annihilator.mp (QuotSMulTop.mem_annihilator (R := A) (M := M) x) mbar
    have hxp : x ∉ p := by
      intro h
      have h0 : x • m' = x • (0 : M) := by rw [smul_zero]; exact (hpm' x).mp h
      exact hm'x (by rw [hx h0]; exact Submodule.zero_mem _)
    have := hpprime
    have : q.IsPrime := hq.isPrime
    have hdrop : ringKrullDim (A ⧸ q) + 1 ≤ ringKrullDim (A ⧸ p) := by
      let xb := Ideal.Quotient.mk p x
      have hxb : xb ∈ nonZeroDivisors (A ⧸ p) := by
        apply mem_nonZeroDivisors_of_ne_zero
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxb
      have h2 : ringKrullDim (A ⧸ q) ≤ ringKrullDim ((A ⧸ p) ⧸ Ideal.span {xb}) := by
        refine ringKrullDim_le_of_surjective
          (Ideal.Quotient.lift (Ideal.span {xb}) (Ideal.Quotient.factor hpq) ?_) ?_
        · intro a ha
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
          rw [map_mul]
          simp [xb, Ideal.Quotient.eq_zero_iff_mem, hxq]
        · exact Ideal.Quotient.lift_surjective_of_surjective _ _
            (Ideal.Quotient.factor_surjective hpq)
      exact (add_le_add_left h2 _).trans h1
    have hIH := ih hrs (fun r hr => hmem r (List.mem_cons_of_mem _ hr)) q hq
    calc ((x :: rs).length : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (A ⧸ q) + 1 := add_le_add_left hIH _
      _ ≤ _ := hdrop
