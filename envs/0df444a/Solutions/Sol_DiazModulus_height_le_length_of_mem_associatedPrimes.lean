-- Prove2me | solution 1 for DiazModulus.height_le_length_of_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T18:19:25.515736+00:00
-- url     : https://prove2.me/submissions/e45b8203-3032-4749-a1b3-1fd0abcb7392

import Mathlib
import Theorems.Thm_DiazModulus_length_le_ringKrullDim_quotient_of_mem_associatedPrimes
import Theorems.Thm_DiazModulus_exists_isRegular_quotient_ofList

open RingTheory.Sequence IsLocalRing

/-! # Local unmixedness: associated primes of `A/(ps)` have height at most `|ps|`

Let `𝔭` be an associated prime of `A/(ps)`; then `A/(ps)` is nontrivial. Since `(ps)·A = (ps)`,
`DiazModulus.exists_isRegular_quotient_ofList` (with `M = A`) gives a regular sequence `ts ⊆ 𝔪` on
`A/(ps)` with `|zs| ≤ |ts| + |ps|`, and
`DiazModulus.length_le_ringKrullDim_quotient_of_mem_associatedPrimes` gives `|ts| ≤ dim A/𝔭`. On the
other side, `ht 𝔭 + dim A/𝔭 ≤ dim A` in any commutative ring: in the prime spectrum, `ht 𝔭` is the
order height of `𝔭`, `dim A/𝔭` its coheight (the primes above `𝔭` are the zero locus of `𝔭`), and the
Krull dimension is the supremum of height plus coheight
(`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`). With `dim A ≤ |zs|`, both `dim A/𝔭` and
`ht 𝔭` are finite, and `ht 𝔭 ≤ |zs| - dim A/𝔭 ≤ |zs| - |ts| ≤ |ps|` is arithmetic in `ℕ`. -/

namespace C12_UL
open DiazModulus

/-- `ht 𝔭 + dim A/𝔭 ≤ dim A`, in any commutative ring. -/
lemma height_add_ringKrullDim_quotient_le {A : Type*} [CommRing A] (p : Ideal A) [hp : p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) ≤ ringKrullDim A := by
  let P : PrimeSpectrum A := ⟨p, hp⟩
  have : Nonempty (PrimeSpectrum A) := ⟨P⟩
  have h1 : p.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  have hS : PrimeSpectrum.zeroLocus (p : Set A) = Set.Ici P := by
    ext q
    exact Iff.rfl
  have h2 : ringKrullDim (A ⧸ p) = Order.coheight P := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici, hS]
  rw [h1, h2, show ringKrullDim A = Order.krullDim (PrimeSpectrum A) from rfl,
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add]
  exact WithBot.coe_le_coe.mpr (le_iSup (fun a => Order.height a + Order.coheight a) P)

end C12_UL

open DiazModulus C12_UL in
theorem solution {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (zs : List A) (hz : RingTheory.Sequence.IsRegular A zs) (hzm : ∀ z ∈ zs, z ∈ IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A ≤ zs.length)
    (ps : List A) (hps : RingTheory.Sequence.IsWeaklyRegular A ps) (hpm : ∀ p ∈ ps, p ∈ IsLocalRing.maximalIdeal A)
    (𝔭 : Ideal A) (h𝔭 : 𝔭 ∈ associatedPrimes A (A ⧸ Ideal.ofList ps)) :
    𝔭.height ≤ ps.length := by
  have : 𝔭.IsPrime := h𝔭.isPrime
  have hI : Ideal.ofList ps • (⊤ : Submodule A A) = Ideal.ofList ps := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [← hI] at h𝔭
  have : Nontrivial (A ⧸ (Ideal.ofList ps • (⊤ : Submodule A A))) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (associatedPrimes.eq_empty_of_subsingleton (R := A)
      (M := A ⧸ (Ideal.ofList ps • (⊤ : Submodule A A)))).subset h𝔭
  obtain ⟨ts, hlen, htm, hts⟩ :=
    DiazModulus.exists_isRegular_quotient_ofList A ps hps hpm zs hz hzm
  have hDL := DiazModulus.length_le_ringKrullDim_quotient_of_mem_associatedPrimes ts
    hts.toIsWeaklyRegular htm 𝔭 h𝔭
  have hHC := height_add_ringKrullDim_quotient_le 𝔭
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (A ⧸ 𝔭) = d := by
    have hle : ringKrullDim (A ⧸ 𝔭) ≤ (zs.length : WithBot ℕ∞) :=
      (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans hdim
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ 𝔭) :=
      (by simp : (0 : WithBot ℕ∞) ≤ (ts.length : WithBot ℕ∞)).trans hDL
    generalize ringKrullDim (A ⧸ 𝔭) = e at hle h0
    induction e with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((zs.length : ℕ∞) : WithBot ℕ∞) := by
          exact_mod_cast hle
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe d => exact ⟨d, rfl⟩
  rw [hd] at hDL hHC
  have hHC' : (𝔭.height : WithBot ℕ∞) + d ≤ zs.length := hHC.trans hdim
  cases hh : 𝔭.height with
  | top =>
    rw [hh] at hHC'
    have h' : (((⊤ : ℕ∞) + d : ℕ∞) : WithBot ℕ∞) ≤ ((zs.length : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast hHC'
    exact absurd (WithBot.coe_le_coe.mp h') (by simp)
  | coe h =>
    rw [hh] at hHC'
    have e1 : h + d ≤ zs.length := by exact_mod_cast hHC'
    have e2 : ts.length ≤ d := by exact_mod_cast hDL
    exact_mod_cast (show h ≤ ps.length by omega)
