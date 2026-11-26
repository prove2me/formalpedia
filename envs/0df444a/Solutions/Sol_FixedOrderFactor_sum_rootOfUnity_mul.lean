-- Prove2me | solution 1 for FixedOrderFactor.sum_rootOfUnity_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:52.510043+00:00
-- url     : https://prove2.me/submissions/ab71eab6-1d5e-43d4-be83-073a74152323

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
public import Theorems.Thm_FixedOrderFactor_rootOfUnity_eq


set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {s : ℕ} (hs : 0 < s) (c : ℕ) :
    ∑ t ∈ range s, rootOfUnity s (c * t) = if s ∣ c then (s : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp s hs.ne'
  set ω := Complex.exp (2 * π * I / s)
  have h : ∀ t, rootOfUnity s (c * t) = (ω ^ c) ^ t := fun t => by
    rw [rootOfUnity_eq, ← pow_mul]
  simp_rw [h]
  by_cases hc : s ∣ c
  · have h1 : ω ^ c = 1 := (hp.pow_eq_one_iff_dvd c).2 hc
    simp [h1, hc]
  · have hne : ω ^ c ≠ 1 := fun h1 => hc ((hp.pow_eq_one_iff_dvd c).1 h1)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm c s, pow_mul, hp.pow_eq_one, one_pow, sub_self,
      zero_div, ite_eq_right_iff.2 (fun h => absurd h hc)]
end FixedOrderFactor
