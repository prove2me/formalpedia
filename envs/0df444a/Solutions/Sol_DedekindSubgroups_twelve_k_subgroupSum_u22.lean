-- Prove2me | solution 1 for DedekindSubgroups.twelve_k_subgroupSum_u22
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:14:58.2477+00:00
-- url     : https://prove2.me/submissions/d5ba3f05-14b6-4e80-b565-968f11a10929

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality
public import Theorems.Thm_DedekindSubgroups_subgroupSum_eq_of_mem_iff
public import Theorems.Thm_DedekindSubgroups_orderOf_u22
public import Theorems.Thm_DedekindSubgroups_mem_zpowers_of_orderOf_three
public import Theorems.Thm_DedekindSubgroups_inv_values
public import Theorems.Thm_DedekindSubgroups_inv_one_eq_zero
public import Theorems.Thm_DedekindSubgroups_meyer


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution : 12 * (63 : ℚ) * subgroupSum (Subgroup.zpowers u22) = 4290 := by
  rw [subgroupSum_eq_of_mem_iff _ _ (fun x => mem_zpowers_of_orderOf_three orderOf_u22)]
  rw [sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have v1 : ((1 : (ZMod 63)ˣ) : ZMod 63).val = 1 := rfl
  have v2 : ((u22 : (ZMod 63)ˣ) : ZMod 63).val = 22 := rfl
  have v3 : ((u22 ^ 2 : (ZMod 63)ˣ) : ZMod 63).val = 43 := rfl
  rw [v1, v2, v3]
  have m1 := meyer (h := 1) (h' := 1) (k := 63) (by norm_num) (by norm_num)
  have m2 := meyer (h := 22) (h' := 43) (k := 63) (by norm_num) (by norm_num)
  have m3 := meyer (h := 43) (h' := 22) (k := 63) (by norm_num) (by norm_num)
  obtain ⟨-, -, i22, i43⟩ := inv_values
  rw [inv_one_eq_zero] at m1
  rw [i22] at m2
  rw [i43] at m3
  push_cast at m1 m2 m3
  linear_combination m1 + m2 + m3
end DedekindSubgroups
