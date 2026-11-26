-- Prove2me | solution 1 for FixedOrderFactor.sum_omega_zpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:37.229718+00:00
-- url     : https://prove2.me/submissions/e1ac57ce-a9f9-4c2c-b218-fec4b5412a5b

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
public import Theorems.Thm_FixedOrderFactor_omega_pow_r

set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r : ℕ} (hr : 0 < r) (e : ℤ) :
    ∑ k : Fin r, ω r ^ ((k : ℤ) * e) = if (r : ℤ) ∣ e then (r : ℂ) else 0 := by
  have hp := Complex.isPrimitiveRoot_exp r hr.ne'
  have h1 : ∀ k : Fin r, ω r ^ ((k : ℤ) * e) = (ω r ^ e) ^ (k : ℕ) := by
    intro k; rw [← zpow_natCast, ← zpow_mul, mul_comm]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ω r ^ e) ^ k) r]
  split_ifs with hd
  · obtain ⟨c, rfl⟩ := hd
    rw [zpow_mul, zpow_natCast, omega_pow_r hr, one_zpow]
    simp
  · have hne : ω r ^ e ≠ 1 := by
      intro h; exact hd ((hp.zpow_eq_one_iff_dvd e).mp h)
    rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      omega_pow_r hr, one_zpow, sub_self, zero_div]
end FixedOrderFactor
