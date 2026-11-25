-- Prove2me | solution 1 for DedekindSubgroups.k_dvd_two_E
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:13:02.379228+00:00
-- url     : https://prove2.me/submissions/b3c54c69-3087-4084-84bb-472f67e0a253

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_six_mul_sum_sq
public import Theorems.Thm_DedekindSubgroups_E_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (h3 : ¬ 3 ∣ k) : (k : ℤ) ∣ 2 * E h k := by
  have hcop : IsCoprime (k : ℤ) 3 := by
    have : Nat.Coprime 3 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    exact Nat.isCoprime_iff_coprime.mpr this.symm
  have hQ : (k : ℤ) ∣ 2 * ∑ r ∈ range k, (r : ℤ) ^ 2 := by
    refine hcop.dvd_of_dvd_mul_left ⟨(k - 1) * (2 * k - 1), ?_⟩
    linear_combination six_mul_sum_sq k
  rw [E_eq]
  obtain ⟨c, hc⟩ := hQ
  exact ⟨h * c - 2 * ∑ r ∈ range k, (r : ℤ) * ((h * r / k : ℕ) : ℤ), by linear_combination h * hc⟩
end DedekindSubgroups
