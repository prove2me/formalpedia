-- Prove2me | solution 1 for Erdos287.exclusive_one_parity_repairs_preserve_layer_patterns
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:24:02.563804+00:00
-- url     : https://prove2.me/submissions/3c6e0ace-08ea-40b7-b58b-f8fe89deb7b7

import Mathlib

open Finset

set_option autoImplicit false

/-- Local deletions on one parity preserve nonadjacency and affect only their
own tested layer when each deleted position has an exclusive layer label. -/
theorem solution (I H P : Finset ℕ) (T : ℕ → Finset ℕ)
    (hH : H ⊆ I) (hsep : ∀ n ∈ H, n + 1 ∉ H)
    (hT : ∀ p ∈ P, ∀ n ∈ T p, n ∈ I ∧ Odd n ∧ n - 1 ∉ H ∧ n + 1 ∉ H)
    (hexclusive : ∀ p ∈ P, ∀ n ∈ T p, ∀ q ∈ P, q ∣ n → p = q) :
    let O := H ∪ P.biUnion T
    H ⊆ O ∧ O ⊆ I ∧ (∀ n ∈ O, n + 1 ∉ O) ∧
      ∀ p ∈ P, (I \ O).filter (fun n => p ∣ n) =
        I.filter (fun n => p ∣ n) \ (H ∪ T p) := by
  classical
  let R := P.biUnion T
  let O := H ∪ R
  change H ⊆ O ∧ O ⊆ I ∧ (∀ n ∈ O, n + 1 ∉ O) ∧
    ∀ p ∈ P, (I \ O).filter (fun n => p ∣ n) = I.filter (fun n => p ∣ n) \ (H ∪ T p)
  have hR (n : ℕ) (hn : n ∈ R) : n ∈ I ∧ Odd n ∧ n - 1 ∉ H ∧ n + 1 ∉ H := by
    obtain ⟨p, hp, hnp⟩ := mem_biUnion.mp hn
    exact hT p hp n hnp
  refine ⟨subset_union_left, union_subset hH (fun n hn => (hR n hn).1), ?_, ?_⟩
  · intro n hn hs
    rcases mem_union.mp hn with hnH | hnR <;> rcases mem_union.mp hs with hsH | hsR
    · exact hsep n hnH hsH
    · exact (hR _ hsR).2.2.1 (by simpa using hnH)
    · exact (hR _ hnR).2.2.2 hsH
    · obtain ⟨i, hi⟩ := (hR _ hnR).2.1
      obtain ⟨j, hj⟩ := (hR _ hsR).2.1
      omega
  · intro p hp
    ext n
    by_cases hpn : p ∣ n
    · have hlocal : n ∈ R ↔ n ∈ T p := by
        constructor
        · intro hn
          obtain ⟨q, hq, hnq⟩ := mem_biUnion.mp hn
          rwa [hexclusive q hq n hnq p hp hpn] at hnq
        · exact fun hn => mem_biUnion.mpr ⟨p, hp, hn⟩
      simp [O, hpn, hlocal]
    · simp [hpn]

