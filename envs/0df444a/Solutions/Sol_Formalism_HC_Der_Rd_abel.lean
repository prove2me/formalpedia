-- Prove2me | solution 1 for Formalism.HC.Der.Rd.abel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:15.529889+00:00
-- url     : https://prove2.me/submissions/bc3101a0-8258-4dc8-a3ac-9b3873c2e780

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_weight_sum
import Theorems.Thm_Formalism_HC_Der_Rd_order_dvd_iff
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
private theorem totient_ne_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.totient ≠ 0 := by
  first
  | exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  | exact (Nat.totient_pos (Nat.pos_of_ne_zero hn)).ne'
  | simpa using hn
variable {N : ℕ} [NeZero N]
private theorem addOrderOf_dvd_of_zmod (x : ZMod N) : addOrderOf x ∣ N :=
  addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
open Classical
namespace Formalism.HC.Der.Rd
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) :
    ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        vonMangoldt (addOrderOf ((u : ZMod N) - 1)) / ((addOrderOf ((u : ZMod N) - 1)).totient : ℝ) =
      ∑ m ∈ N.divisors, vonMangoldt m * rho U (N / m) := by
  have hN : N ≠ 0 := NeZero.ne N
  have hT : (N.totient : ℝ) ≠ 0 := by exact_mod_cast totient_ne_zero_of_ne_zero hN
  calc _ = ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        ∑ m ∈ N.divisors, (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.mem_filter] at hu
        have hd : addOrderOf ((u : ZMod N) - 1) ∣ N := addOrderOf_dvd_of_zmod _
        have h1 : addOrderOf ((u : ZMod N) - 1) ≠ 1 := by
          intro h
          have h' := addOrderOf_nsmul_eq_zero ((u : ZMod N) - 1)
          rw [h, one_nsmul, sub_eq_zero] at h'
          exact hu.2 (by rw [show u = 1 from Units.ext (by rw [h', Units.val_one])]; exact one_mem U)
        rw [← Finset.sum_filter, ← Finset.sum_div, weight_sum hN hd h1, eq_div_iff hT]
        ring
    _ = ∑ m ∈ N.divisors, ∑ u ∈ (univ : Finset (ZMod N)ˣ).filter (fun u => u ∉ U),
        (if addOrderOf ((u : ZMod N) - 1) ∣ m then
          vonMangoldt m * ((N / m).totient : ℝ) / N.totient else 0) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun m hm => ?_
        have hmN : m ∣ N := Nat.dvd_of_mem_divisors hm
        have hcard : (((univ : Finset (ZMod N)ˣ).filter (fun u : (ZMod N)ˣ => u ∉ U)).filter
            (fun u : (ZMod N)ˣ => addOrderOf ((u : ZMod N) - 1) ∣ m)).card =
            ((KK N (N / m)).filter fun u => u ∉ U).card := by
          apply congrArg Finset.card
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_KK,
            order_dvd_iff hmN]
          tauto
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard]
        unfold rho
        ring
end Formalism.HC.Der.Rd
