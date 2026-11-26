-- Prove2me | solution 1 for Erdos266.aSeq_large
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:28.17655+00:00
-- url     : https://prove2.me/submissions/f6db7d6f-ed46-49c4-82f0-371b31fdf50e

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_jOf_lt
public import Theorems.Thm_Erdos266_le_kOf_of_cnt_le
public import Theorems.Thm_Erdos266_elemZ_lb
public import Theorems.Thm_Erdos266_aSeq_cast
public import Theorems.Thm_Erdos266_le_bigN
public import Theorems.Thm_Erdos266_two_mul_bigM_lt


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution {i' m : ℕ} (hm : cnt (4 * i' + 4) ≤ m) :
    (2 * (i' + 1) : ℝ) ≤ ((aSeq m : ℕ) : ℝ) := by
  have hk : 4 * i' + 4 ≤ kOf m := le_kOf_of_cnt_le hm
  have hN : (4 * (i' + 1) : ℕ) ≤ bigN (kOf m) := by
    have := le_bigN (kOf m)
    omega
  have hM : 2 * bigM (kOf m) < bigN (kOf m) := two_mul_bigM_lt (by omega)
  have hlb := elemZ_lb (jOf_lt m)
  have hcast := aSeq_cast m
  have hZ : (2 * (i' + 1) : ℤ) ≤ (aSeq m : ℤ) := by
    have hN' : (4 * (i' + 1) : ℤ) ≤ (bigN (kOf m) : ℤ) := by exact_mod_cast hN
    have hM' : 2 * (bigM (kOf m) : ℤ) < (bigN (kOf m) : ℤ) := by exact_mod_cast hM
    omega
  exact_mod_cast hZ
end Erdos266
