-- Prove2me | solution 1 for DedekindSubgroups.two_mul_dedekindSum_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:14:15.989436+00:00
-- url     : https://prove2.me/submissions/5754f53c-9ce7-437f-a417-073802864f80

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_E_cast
public import Theorems.Thm_DedekindSubgroups_k_dvd_two_E
public import Theorems.Thm_DedekindSubgroups_dedekindSum_residue


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) (h3 : ¬ 3 ∣ k) :
    ∃ c : ℤ, (c : ℚ) = 2 * k * dedekindSum h k := by
  obtain ⟨c, hc⟩ := k_dvd_two_E (h := h) h3
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self ((k : ℤ) - 1)
  refine ⟨c - j, ?_⟩
  rw [dedekindSum_residue hk hinv, ← E_cast]
  have hc' : (2 : ℚ) * E h k = k * c := by exact_mod_cast hc
  have hj' : ((k : ℚ) - 1) * ((k : ℚ) - 1 + 1) = j + j := by exact_mod_cast hj
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [show (2 : ℚ) * k * ((E h k : ℚ) / k ^ 2 - ((k : ℚ) - 1) / 4)
      = (2 * E h k) / k - ((k : ℚ) - 1) * ((k : ℚ) - 1 + 1) / 2 by field_simp; ring, hc', hj']
  field_simp
  ring
end DedekindSubgroups
