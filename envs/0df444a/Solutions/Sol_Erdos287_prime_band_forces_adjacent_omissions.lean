-- Prove2me | solution 1 for Erdos287.prime_band_forces_adjacent_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:22:45.820809+00:00
-- url     : https://prove2.me/submissions/9d054db1-e114-42b9-802d-54f087be8f05

import Mathlib
import Theorems.Thm_Erdos287_few_prime_layers_with_few_omissions

open Finset

set_option autoImplicit false

/-- If too many prime layers leave too few positions away from known
omissions, a new omitted multiple must be adjacent to a known omission. -/
theorem solution (D H P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1))
    (hfew : ∀ p ∈ P,
      ((Finset.Icc ((m - 1) / p + 1) (M / p)).filter
        (fun c => c * p - 1 ∉ H ∧ c * p + 1 ∉ H)).card < R)
    (hmany : ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K < P.card) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D ∧ (n ∈ H ∨ n + 1 ∈ H) := by
  classical
  let C (p : ℕ) := Icc ((m - 1) / p + 1) (M / p)
  let A (p : ℕ) := (C p).filter (fun c => c * p ∉ D)
  let Q := P.filter (fun p => (A p).card < R)
  by_contra hno
  have hsub : P ⊆ Q := by
    intro p hp
    apply mem_filter.mpr
    refine ⟨hp, lt_of_le_of_lt (card_le_card ?_) (hfew p hp)⟩
    intro c hc
    obtain ⟨hcC, hcD⟩ := mem_filter.mp hc
    obtain ⟨hcl, hcu⟩ := mem_Icc.mp hcC
    have hp0 := (hP p hp).1.pos
    have hlo : m - 1 < c * p := (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_of_succ_le hcl)
    have hmcp : m ≤ c * p := by omega
    have hhi : c * p ≤ M := (Nat.le_div_iff_mul_le hp0).mp hcu
    apply mem_filter.mpr
    refine ⟨hcC, ?_, ?_⟩
    · intro hh
      have hleft := (mem_Icc.mp (hH hh)).1
      have he : c * p - 1 + 1 = c * p := by omega
      refine hno ⟨c * p - 1, hleft, he.symm ▸ hhi,
        disjoint_left.mp hHD hh, he.symm ▸ hcD, Or.inl hh⟩
    · intro hh
      have hright := (mem_Icc.mp (hH hh)).2
      exact hno ⟨c * p, hmcp, hright, hcD, disjoint_left.mp hHD hh, Or.inr hh⟩
  have hQ := Erdos287.few_prime_layers_with_few_omissions D P m M B Y K R hm hmM hD hsum
    hY hP hbound
  exact (hmany.not_ge ((card_le_card hsub).trans hQ))

