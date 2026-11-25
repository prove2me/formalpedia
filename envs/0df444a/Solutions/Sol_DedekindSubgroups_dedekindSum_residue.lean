-- Prove2me | solution 1 for DedekindSubgroups.dedekindSum_residue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:07:37.025409+00:00
-- url     : https://prove2.me/submissions/7c360d4c-b532-44c1-a37e-e24e8fc6b452

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
public import Theorems.Thm_DedekindSubgroups_one_lt_of_inv
public import Theorems.Thm_DedekindSubgroups_sum_sig_perm
public import Theorems.Thm_DedekindSubgroups_sawtooth_div_of_lt
public import Theorems.Thm_DedekindSubgroups_sawtooth_mul_div
public import Theorems.Thm_DedekindSubgroups_sum_range_cast_id

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) :
    dedekindSum h k = (∑ r ∈ range k, (r : ℚ) * sig h k r) / (k : ℚ) ^ 2 - ((k : ℚ) - 1) / 4 := by
  have hk1 := one_lt_of_inv hk hinv
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h0 : sig h k 0 = 0 := by simp [sig]
  have hterm : ∀ r ∈ range k,
      sawtooth ((r : ℚ) / k) * sawtooth ((h * r : ℚ) / k)
        = (r : ℚ) * sig h k r / (k : ℚ) ^ 2 - (sig h k r : ℚ) / (2 * k) - (r : ℚ) / (2 * k) + 1 / 4
          - (if r = 0 then 1 / 4 else 0) := by
    intro r hr
    rw [mem_range] at hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [sawtooth, h0]
    · rw [sawtooth_div_of_lt hr0 hr, sawtooth_mul_div hinv hr0 hr, if_neg hr0.ne']
      field_simp
      ring
  unfold dedekindSum
  rw [sum_congr rfl hterm]
  simp only [sum_sub_distrib, sum_add_distrib, ← sum_div, sum_const, card_range, nsmul_eq_mul,
    sum_ite_eq', mem_range, if_pos hk]
  have hS : (∑ r ∈ range k, (sig h k r : ℚ)) = ∑ r ∈ range k, (r : ℚ) :=
    sum_sig_perm hk hinv (fun z => (z : ℚ))
  rw [hS, sum_range_cast_id]
  field_simp
  ring
end DedekindSubgroups
