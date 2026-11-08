-- Prove2me | solution 1 for CVStabilizer.weyl_comm
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:25:08.708198+00:00
-- url     : https://prove2.me/submissions/0c0bfbee-e580-4f7e-855e-ee466a952887

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

open CVStabilizer in
theorem solution (n : ℕ) (v v' : CVStabilizer.PhaseSpace n) :
    CVStabilizer.weyl v ∘ CVStabilizer.weyl v' =
      (fun ψ => Complex.exp (((Real.pi * CVStabilizer.omega n v v' : ℝ) : ℂ) * Complex.I) • ψ)
        ∘ CVStabilizer.weyl v' ∘ CVStabilizer.weyl v := by
  funext ψ x
  simp only [Function.comp_apply, CVStabilizer.weyl, CVStabilizer.omega_apply, Pi.smul_apply,
    smul_eq_mul]
  have hx : x + v.1 + v'.1 = x + v'.1 + v.1 := by abel
  rw [hx]
  have key : ((∑ i, v.2 i * x i) + (∑ i, v.1 i * v.2 i) / 2) +
      ((∑ i, v'.2 i * (x + v.1) i) + (∑ i, v'.1 i * v'.2 i) / 2) =
      (∑ i, (v.1 i * v'.2 i - v'.1 i * v.2 i)) +
      ((∑ i, v'.2 i * x i) + (∑ i, v'.1 i * v'.2 i) / 2) +
      ((∑ i, v.2 i * (x + v'.1) i) + (∑ i, v.1 i * v.2 i) / 2) := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ i, v'.2 i * v.1 i = ∑ i, v.1 i * v'.2 i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have e2 : ∑ i, v.2 i * v'.1 i = ∑ i, v'.1 i * v.2 i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e1, e2]
    ring
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  rw [← add_mul, ← add_mul, ← add_mul]
  congr 1
  rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
  congr 1
  linear_combination Real.pi * key
