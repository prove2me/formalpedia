-- Prove2me | solution 1 for Erdos287.prime_band_omission_budget
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:22:54.964906+00:00
-- url     : https://prove2.me/submissions/d96fbf8b-60d9-4273-bf49-b981fbe66b1a

import Mathlib
import Theorems.Thm_Erdos287_few_prime_layers_with_few_omissions
import Theorems.Thm_Erdos287_additional_omission_mass_from_prime_layers

open Finset

set_option autoImplicit false

/-- An exact reciprocal representation must leave room for a prime band's
guaranteed omissions after all prior certified omissions are counted. -/
theorem solution (D H P : Finset ℕ) (m M B Y K R : ℕ) (hm : 0 < m) (hmM : m ≤ M)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : H ⊆ Finset.Icc m M) (hHD : Disjoint H D)
    (hYM : M < Y ^ 2) (hY : 2 ≤ Y)
    (hP : ∀ p ∈ P, p.Prime ∧ Y ≤ p ∧ M / p ≤ B ∧
      R ≤ (Finset.Icc ((m - 1) / p + 1) (M / p)).card)
    (hsep : ∀ p ∈ P, ∀ n ∈ H, ¬ p ∣ n)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    let E := ((B + 1) * (B + 1)) * (∑ j ∈ Finset.range R, B.choose j) * K
    1 + (∑ n ∈ H, (1 : ℚ) / n) + ((R * (P.card - E) : ℕ) : ℚ) / M
      ≤ ∑ n ∈ Finset.Icc m M, (1 : ℚ) / n := by
  intro E
  let A (p : ℕ) := (Icc ((m - 1) / p + 1) (M / p)).filter (fun c => c * p ∉ D)
  let Good := P.filter (fun p => R ≤ (A p).card)
  have hgoodP : Good ⊆ P := filter_subset _ _
  have hbad : (P.filter (fun p => (A p).card < R)).card ≤ E :=
    Erdos287.few_prime_layers_with_few_omissions D P m M B Y K R hm hmM hD hsum hY hP hbound
  have hsplit : Good.card + (P.filter (fun p => (A p).card < R)).card = P.card := by
    simpa only [Good, not_le] using P.card_filter_add_card_filter_not (fun p => R ≤ (A p).card)
  have hcard : P.card - E ≤ Good.card := by omega
  have hactual := Erdos287.additional_omission_mass_from_prime_layers
    D H Good m M Y R hm hmM hD hsum hH hHD hYM
    (fun p hp => ⟨(hP p (hgoodP hp)).1, (hP p (hgoodP hp)).2.1⟩)
    (fun p hp => hsep p (hgoodP hp))
    (fun p hp => (mem_filter.mp hp).2)
  refine le_trans ?_ hactual
  apply add_le_add_right
  apply (div_le_div_iff_of_pos_right (show (0 : ℚ) < M by exact_mod_cast hm.trans_le hmM)).mpr
  exact_mod_cast Nat.mul_le_mul_left R hcard

