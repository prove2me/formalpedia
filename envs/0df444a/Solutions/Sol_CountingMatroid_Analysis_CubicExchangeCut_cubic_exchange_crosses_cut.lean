-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicExchangeCut.cubic_exchange_crosses_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:02.095518+00:00
-- url     : https://prove2.me/submissions/9b257765-6d16-4d39-ba6c-e260ba0af385

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature

namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
set_option autoImplicit false

/-!
Exchange support prevents a cubic tensor from splitting into two nonzero
blocks with no entry joining them. This is the combinatorial input to the
spectral local-to-global argument; no spectral conclusion is asserted here.
-/

namespace CountingMatroid.Analysis.CubicExchangeCut
end CountingMatroid.Analysis.CubicExchangeCut
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicExchangeCut

/-- INTERNAL: A degree-three exchange support has no separation into two
active coordinate blocks. The cut conclusion is the irreducibility input
needed for the normalized contraction's maximum principle.
TEXLINE: main.tex:340-347 -/
theorem solution {σ : Type} [DecidableEq σ]
    (T : σ → σ → σ → ℚ)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (S : Set (σ →₀ ℕ))
    (hsupport : ∀ x, x ∈ S ↔ ∃ s i j, T s i j ≠ 0 ∧
      x = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1)
    (hex : ∀ x ∈ S, ∀ y ∈ S, ∀ i, y i < x i →
      ∃ j, x j < y j ∧ x - Finsupp.single i 1 + Finsupp.single j 1 ∈ S)
    (U : Set σ)
    (hin : ∃ s i j, T s i j ≠ 0 ∧ s ∈ U)
    (hout : ∃ s i j, T s i j ≠ 0 ∧ s ∉ U) :
    ∃ s i j, T s i j ≠ 0 ∧ i ∈ U ∧ j ∉ U := by
  classical
  by_contra hn
  have hpair (s i j : σ) (ht : T s i j ≠ 0) : i ∈ U ↔ j ∈ U := by
    constructor
    · intro hi
      by_contra hj
      exact hn ⟨s, i, j, ht, hi, hj⟩
    · intro hj
      by_contra hi
      exact hn ⟨s, j, i, by rwa [hlast s j i], hj, hi⟩
  have hfirst (s i j : σ) (ht : T s i j ≠ 0) : s ∈ U ↔ i ∈ U := by
    apply hpair j s i
    rwa [hswap j s i, hlast s j i]
  obtain ⟨s, i, j, ht, hs⟩ := hin
  obtain ⟨t, a, b, hu, htout⟩ := hout
  have hi : i ∈ U := (hfirst s i j ht).mp hs
  have hj : j ∈ U := (hpair s i j ht).mp hi
  have ha : a ∉ U := fun h => htout ((hfirst t a b hu).mpr h)
  have hb : b ∉ U := fun h => ha ((hpair t a b hu).mpr h)
  let x := Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1
  let y := Finsupp.single a 1 + Finsupp.single b 1 + Finsupp.single t 1
  have hx : x ∈ S := (hsupport x).mpr ⟨s, i, j, ht, rfl⟩
  have hy : y ∈ S := (hsupport y).mpr ⟨t, a, b, hu, rfl⟩
  have hyzero (c : σ) (hc : c ∈ U) : y c = 0 := by
    have hca : a ≠ c := fun h => ha (h ▸ hc)
    have hcb : b ≠ c := fun h => hb (h ▸ hc)
    have hct : t ≠ c := fun h => htout (h ▸ hc)
    simp [y, Finsupp.single_apply, hca, hcb, hct]
  have hxs : 0 < x s := by
    simp only [x, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  obtain ⟨k, hk, hz⟩ := hex x hx y hy s (by rw [hyzero s hs]; exact hxs)
  have hkout : k ∉ U := by
    intro hku
    rw [hyzero k hku] at hk
    omega
  let z := x - Finsupp.single s 1 + Finsupp.single k 1
  have hzi : 0 < z i := by
    simp only [z, x, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hzk : 0 < z k := by
    simp only [z, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, if_pos, add_zero]
    omega
  obtain ⟨p, q, r, hv, heq⟩ := (hsupport z).mp hz
  have hall : (q ∈ U ∧ r ∈ U ∧ p ∈ U) ∨
      (q ∉ U ∧ r ∉ U ∧ p ∉ U) := by
    by_cases hp : p ∈ U
    · have hq := (hfirst p q r hv).mp hp
      exact Or.inl ⟨hq, (hpair p q r hv).mp hq, hp⟩
    · have hq : q ∉ U := fun h => hp ((hfirst p q r hv).mpr h)
      exact Or.inr ⟨hq, fun h => hq ((hpair p q r hv).mpr h), hp⟩
  rcases hall with ⟨hq, hr, hp⟩ | ⟨hq, hr, hp⟩
  · have hqk : q ≠ k := fun h => hkout (h ▸ hq)
    have hrk : r ≠ k := fun h => hkout (h ▸ hr)
    have hpk : p ≠ k := fun h => hkout (h ▸ hp)
    rw [heq] at hzk
    simp [Finsupp.single_apply, hqk, hrk, hpk] at hzk
  · have hqi : q ≠ i := fun h => hq (h ▸ hi)
    have hri : r ≠ i := fun h => hr (h ▸ hi)
    have hpi : p ≠ i := fun h => hp (h ▸ hi)
    rw [heq] at hzi
    simp [Finsupp.single_apply, hqi, hri, hpi] at hzi
