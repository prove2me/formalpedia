-- Prove2me | solution 1 for DiazModulus.exists_isWeaklyRegular_append_of_height
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-29T08:19:21.068378+00:00
-- url     : https://prove2.me/submissions/afc2312a-ff14-4c11-ad3c-315ea255826c

import Definitions.Def_DiazHilbertBox
import Theorems.Thm_DiazModulus_exists_mem_isSMulRegular_of_associatedPrimes

open Complex ComplexConjugate

/-! # Extending a weakly regular sequence inside a subspace, by height

Let `S` be a Noetherian `K`-algebra over an infinite field satisfying (U) (`UnmixedHeight S`), let
`ps₀` be weakly regular and `V` a `K`-subspace of `S` such that every prime over `(ps₀) + (V)` has
height at least `|ps₀| + r`. Then `r` elements of `V` extend `ps₀` to a weakly regular sequence.
Induction on `m ≤ r`: suppose `L = ps₀ ++ rs` is weakly regular with `rs ⊆ V` of length `m < r`.
Every associated prime `p` of `S ⧸ (L)` contains `(L) ⊇ (ps₀)` (it contains the annihilator of
`S ⧸ (L)`, `IsAssociatedPrime.annihilator_le`), and (U) bounds its height by `|L| = |ps₀| + m`.
If `V ⊆ p` then `p` lies over `(ps₀) + (V)` and the height hypothesis gives `|ps₀| + r ≤ |ps₀| + m`,
which is false; so `V ⊄ p`. The node `exists_mem_isSMulRegular_of_associatedPrimes` (applied to
the finite module `S ⧸ (L)`) gives `x ∈ V` regular on `S ⧸ (L)`, and `ps₀ ++ (rs ++ [x])` is weakly
regular by `isWeaklyRegular_append_iff` (with `(L) • ⊤ = (L)`, `Ideal.mul_top`). If `S ⧸ (L) = 0`
there are no associated primes and the step is the same. -/

namespace C11_R5

theorem le_of_mem_associatedPrimes {S : Type*} [CommRing S] (I p : Ideal S)
    (hp : p ∈ associatedPrimes S (S ⧸ I)) : I ≤ p := by
  refine le_trans ?_ (IsAssociatedPrime.annihilator_le hp)
  intro a ha
  rw [Submodule.mem_annihilator]
  intro m _
  induction m using Submodule.Quotient.induction_on with
  | H b =>
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
    exact I.mul_mem_right b ha

end C11_R5

open DiazModulus C11_R5 in
theorem solution {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    [IsNoetherianRing S] [Infinite K]
    (hU : UnmixedHeight S)
    (ps₀ : List S) (hps₀ : RingTheory.Sequence.IsWeaklyRegular S ps₀) (V : Submodule K S) (r : ℕ)
    (hH : ∀ p : Ideal S, p.IsPrime → Ideal.ofList ps₀ ⊔ Ideal.span (V : Set S) ≤ p →
      ((ps₀.length + r : ℕ) : ℕ∞) ≤ p.height) :
    ∃ rs : List S, rs.length = r ∧ (∀ x ∈ rs, x ∈ V) ∧
      RingTheory.Sequence.IsWeaklyRegular S (ps₀ ++ rs) := by
  suffices key : ∀ m ≤ r, ∃ rs : List S, rs.length = m ∧ (∀ x ∈ rs, x ∈ V) ∧
      RingTheory.Sequence.IsWeaklyRegular S (ps₀ ++ rs) from key r le_rfl
  intro m
  induction m with
  | zero => exact fun _ => ⟨[], rfl, by simp, by simpa using hps₀⟩
  | succ m ih =>
    intro hm
    obtain ⟨rs, hlen, hV, hreg⟩ := ih (by omega)
    set L := ps₀ ++ rs with hL
    have havoid : ∀ p ∈ associatedPrimes S (S ⧸ Ideal.ofList L),
        ¬ (V : Set S) ⊆ (p : Set S) := by
      intro p hp hVp
      have hprime : p.IsPrime := IsAssociatedPrime.isPrime hp
      have hht := hU L hreg p hp
      have hle : Ideal.ofList ps₀ ⊔ Ideal.span (V : Set S) ≤ p := by
        refine sup_le ?_ (Ideal.span_le.mpr hVp)
        refine le_trans ?_ (le_of_mem_associatedPrimes _ p hp)
        rw [hL, Ideal.ofList_append]
        exact le_sup_left
      have h1 := hH p hprime hle
      have h2 : ((ps₀.length + r : ℕ) : ℕ∞) ≤ (L.length : ℕ∞) := h1.trans hht
      have h3 : ps₀.length + r ≤ L.length := by exact_mod_cast h2
      simp [hL, hlen] at h3
      omega
    obtain ⟨x, hxV, hx⟩ :=
      DiazModulus.exists_mem_isSMulRegular_of_associatedPrimes (M := S ⧸ Ideal.ofList L) V havoid
    refine ⟨rs ++ [x], by simp [hlen], ?_, ?_⟩
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hV y hy
      · rw [List.mem_singleton.mp hy]; exact hxV
    · rw [← List.append_assoc, ← hL, RingTheory.Sequence.isWeaklyRegular_append_iff]
      refine ⟨hreg, ?_⟩
      rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      have hI : (Ideal.ofList L • ⊤ : Submodule S S) = Ideal.ofList L := by
        rw [smul_eq_mul, Ideal.mul_top]
      exact (Submodule.quotEquivOfEq _ _ hI).isSMulRegular_congr x |>.mpr hx
